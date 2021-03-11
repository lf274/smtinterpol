package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.bitvector;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.BooleanVarAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom.TrueAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.SourceAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.epr.util.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedArrayList;

public class BitBlaster {

	private final Theory mTheory;
	private final ScopedArrayList<Literal> mInputLiterals;
	private final LinkedHashSet<Term> mAllTerms;
	private final HashMap<String, TermVariable> mVarPrefix; // Maps enc_term indices to their bool vars.
	private final HashMap<Term, DPLLAtom> mBoolAtoms; // All Bool Atoms, aux varaibles too
	private final ScopedArrayList<Clause> mClauses; // Output clauses
	private final HashMap<Term, Term[]> mEncTerms; // Term[0] is the least bit, the most right bit of Term
	private final HashMap<String, Term> mEncAtoms; // Maps Prefix At_i to bool atom
	private final HashMap<Term, Literal> mLiterals; // Maps mEncAtoms to mInputLiterals
	private final BVUtils mBVUtils;
	private final int mStackLevel;

	public BitBlaster(final Theory theory, final int engineStackLevel, final ScopedArrayList<Literal> allLiterals,
			final LinkedHashSet<Term> allTerms) {
		mTheory = theory;
		mInputLiterals = allLiterals;
		mAllTerms = allTerms;
		mVarPrefix = new HashMap<>();
		mEncTerms = new HashMap<>();
		mEncAtoms = new HashMap<>();
		mBVUtils = new BVUtils(mTheory);
		mBoolAtoms = new HashMap<>();
		mLiterals = new HashMap<>();
		mClauses = new ScopedArrayList<>();
		mStackLevel = engineStackLevel;
	}

	public void bitBlasting() {
		Term equisatProp;
		final Term[] propSkeleton = new Term[mInputLiterals.size()];
		for (int i = 0; i < mInputLiterals.size(); i++) {
			final String atomPrefix = "At_" + i;
			final TermVariable boolVar = mTheory.createFreshTermVariable(atomPrefix, mTheory.getSort("Bool"));
			mEncAtoms.put(atomPrefix, boolVar);
			mBoolAtoms.put(boolVar, new BooleanVarAtom(boolVar, mStackLevel));
			mLiterals.put(boolVar, mInputLiterals.get(i));
			if (mInputLiterals.get(i).getSign() == -1) {
				propSkeleton[i] = mTheory.not(boolVar);
			} else {
				propSkeleton[i] = boolVar;
			}
		}
		for (final Term term : mAllTerms) {
			// e(t), t in terms. Terms Size long Array of bool vars with e(t)_i being var at position i
			if (term.getSort().isBitVecSort()) {
				mEncTerms.put(term, getEncodedTerm(term));
			}
		}
		// Initial propositional configuration
		equisatProp = mTheory.and(propSkeleton); // TODO Input always conjunction?
		toClauses(equisatProp);

		// add BVConstraint of Atoms as conjunct
		for (int i = 0; i < mInputLiterals.size(); i++) {
			final DPLLAtom atom = mInputLiterals.get(i).getAtom();
			final Term encAtom = mEncAtoms.get("At_" + i);
			getBvConstraintAtom(encAtom, atom);
		}
		// add BVConstraint of all subterms as conjunct
		for (final Term term : mAllTerms) {
			getBvConstraintTerm(term);
		}
	}

	/*
	 * Encodes bitvector Term in an Array of same lenth as the size of the bitvector Term.
	 * The Array contains Fresh Boolean Variables with name:
	 * "e(term)_i" where e stands for encoded, term is the input term and i the current position in the Array/BitVec
	 */
	private Term[] getEncodedTerm(final Term term) {
		assert term.getSort().isBitVecSort();
		final BigInteger sizeBig = mTheory.toNumeral(term.getSort().getIndices()[0]);
		final int size = sizeBig.intValue();

		final Term[] boolvector = new Term[size];
		for (int i = 0; i < size; i++) {
			final String termPrefix = "e(" + term + ")_" + i;
			final TermVariable tv = mVarPrefix.get(termPrefix);
			final TermVariable boolVar;
			if (tv != null) {
				boolVar = tv;
			} else {
				boolVar = mTheory.createFreshTermVariable(termPrefix, mTheory.getSort("Bool"));
				mBoolAtoms.put(boolVar, new BooleanVarAtom(boolVar, mStackLevel));
				mVarPrefix.put(termPrefix, boolVar);
			}
			boolvector[i] = boolVar;
		}
		return boolvector;
	}

	/*
	 * Creates BVConstraint for Atom's
	 * For equals:
	 * (AND lhs_i = rhs_i) <=> encAtom
	 */
	private void getBvConstraintAtom(final Term encAtom, final DPLLAtom atom) {
		if (atom instanceof BVEquality) {
			// (AND lhs_i = rhs_i) <=> encAtom
			final BVEquality bveqatom = (BVEquality) atom;
			final BigInteger sizeBig = mTheory.toNumeral(bveqatom.getLHS().getSort().getIndices()[0]);
			final int size = sizeBig.intValue();
			final Term[] eqconj = new Term[size + size];
			for (int i = 0; i < size; i++) {
				eqconj[i] =
						mTheory.or(mTheory.not(mEncTerms.get(bveqatom.getLHS())[i]),
								mEncTerms.get(bveqatom.getRHS())[i]);
				eqconj[i + size] =
						mTheory.or(mTheory.not(mEncTerms.get(bveqatom.getRHS())[i]),
								mEncTerms.get(bveqatom.getLHS())[i]);
			}
			final Term eqconjunction = mTheory.and(eqconj);
			toClauses(mTheory.and(mTheory.or(mTheory.not(encAtom), eqconjunction),
					mTheory.or(mTheory.not(eqconjunction), encAtom)));

		} else if (atom instanceof BVInEquality) {
			final BVInEquality bvIneqatom = (BVInEquality) atom;
			// bvult, holds if cout is false
			final Term bvult =
					mTheory.not(adder(mEncTerms.get(bvIneqatom.getLHS()), negate(mEncTerms.get(bvIneqatom.getRHS())),
							mTheory.mTrue).getSecond());
			toClauses(mTheory.and(mTheory.or(mTheory.not(encAtom), bvult),
					mTheory.or(mTheory.not(bvult), encAtom)));


		} else {
			throw new UnsupportedOperationException("Unknown Atom");
		}
	}

	/*
	 * Bitblasting for all terms, reports the result as Clause to mClauses
	 */
	private void getBvConstraintTerm(final Term term) {
		if (term instanceof TermVariable) {
			return;
		} else if (term instanceof ConstantTerm) {
			final Term[] encTerm = mEncTerms.get(term);
			final Term[] constresult = new Term[encTerm.length];
			for (int i = 0; i < encTerm.length; i++) {
				Term boolVar;
				final String termstring = BVUtils.getConstAsString((ConstantTerm) term);
				if (termstring.charAt(termstring.length() - 1 - i) == '1') {
					boolVar = mTheory.mTrue;
				} else {
					boolVar = mTheory.mFalse;
				}
				mBoolAtoms.put(boolVar, new BooleanVarAtom(boolVar, mStackLevel));
				final Term ifte = mTheory.and(mTheory.or(mTheory.not(encTerm[i]), boolVar),
						mTheory.or(mTheory.not(boolVar), encTerm[i]));

				addClauses(mTheory.or(mTheory.not(encTerm[i]), boolVar));
				addClauses(mTheory.or(mTheory.not(boolVar), encTerm[i]));
				constresult[i] = ifte;
			}
		} else if (term instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) term;
			final FunctionSymbol fsym = appterm.getFunction();
			if (appterm.getParameters().length == 0) {
				// Variable but not instanceof TermVariable
				return;
			}
			if (fsym.isIntern()) {
				switch (fsym.getName()) {
				case "=":
				case "and":
				case "or":
				case "not":
				case "ite": {
					return;
				}
				}
				final Term[] encTerm = mEncTerms.get(term);
				Term[] conjunction = new Term[encTerm.length];
				switch (fsym.getName()) {
				case "bvand": {
					for (int i = 0; i < encTerm.length; i++) {
						final Term and = mTheory.and(mEncTerms.get(appterm.getParameters()[0])[i],
								mEncTerms.get(appterm.getParameters()[1])[i]);
						conjunction[i] = and;
					}
					break;
				}
				case "bvor": {
					for (int i = 0; i < encTerm.length; i++) {
						final Term or = mTheory.or(mEncTerms.get(appterm.getParameters()[0])[i],
								mEncTerms.get(appterm.getParameters()[1])[i]);
						conjunction[i] = or;
					}
					break;
				}
				case "bvnot": {
					for (int i = 0; i < encTerm.length; i++) {
						final Term not = mTheory.not(mEncTerms.get(appterm.getParameters()[0])[i]);
						conjunction[i] = not;
					}
					break;
				}
				case "bvneg": {
					conjunction[encTerm.length - 1] =
							mTheory.not(mEncTerms.get(appterm.getParameters()[0])[encTerm.length - 1]);
					for (int i = 0; i < encTerm.length - 1; i++) {
						conjunction[i] = mEncTerms.get(appterm.getParameters()[0])[i];
					}
					break;
				}
				case "bvadd": {
					conjunction =
							adder(mEncTerms.get(appterm.getParameters()[0]), mEncTerms.get(appterm.getParameters()[1]),
									mTheory.mFalse).getFirst();
					break;
				}
				case "bvsub": {
					conjunction =
							adder(mEncTerms.get(appterm.getParameters()[0]),
									negate(mEncTerms.get(appterm.getParameters()[1])),
									mTheory.mTrue).getFirst();
					break;
				}
				case "bvshl": {
					final int stage =
							mTheory.toNumeral(appterm.getParameters()[1].getSort().getIndices()[0]).intValue() - 1;
					conjunction = shift(appterm.getParameters()[0], appterm.getParameters()[1], stage, true);
					break;
				}
				case "bvmul": {
					final int stage =
							mTheory.toNumeral(appterm.getParameters()[1].getSort().getIndices()[0]).intValue() - 1;
					conjunction = multiplier(appterm.getParameters()[0], appterm.getParameters()[1], stage);
					break;
				}

				case "bvlshr": {
					final int stage =
							mTheory.toNumeral(appterm.getParameters()[1].getSort().getIndices()[0]).intValue() - 1;
					conjunction = shift(appterm.getParameters()[0], appterm.getParameters()[1], stage, false);
					break;
				}
				case "concat": {
					conjunction = concatArrays(mEncTerms.get(appterm.getParameters()[0]),
							mEncTerms.get(appterm.getParameters()[1]));
					break;
				}
				case "extract": {
					conjunction = Arrays.copyOfRange(mEncTerms.get(appterm.getParameters()[0]),
							Integer.parseInt(appterm.getFunction().getIndices()[1]),
							Integer.parseInt(appterm.getFunction().getIndices()[0]) + 1);
					break;
				}
				case "bvudiv": {
					// b != 0 => e(t) * b + r = a
					// b != 0 => r < b
				}
				case "bvurem":
					// b != 0 => q * b + e(t) = a
					// b != 0 => e(t) < b
					// Add Aux vars for each step
					final Term[] encA  = mEncTerms.get(appterm.getParameters()[0]);
					final Term[] encB = mEncTerms.get(appterm.getParameters()[1]);
					final int stage =
							mTheory.toNumeral(appterm.getParameters()[1].getSort().getIndices()[0]).intValue() - 1;
					final Term[] remainder;
					final Term[] product;
					if (fsym.getName().equals("bvudiv")) {
						remainder = createBoolVarArray(conjunction.length);
						product = multiplier(encTerm, encB, stage);
					} else if (fsym.getName().equals("bvurem")) {
						remainder = encTerm;
						product = multiplier(createBoolVarArray(conjunction.length), encB, stage);
					} else {
						throw new UnsupportedOperationException(
								"Unsupported functionsymbol for bitblasting: " + fsym.getName());
					}
					for (int i = 0; i < product.length; i++) {
						product[i] = createAuxVar(product[i]);
					}
					final Term[] sum = adder(product, remainder, mTheory.mFalse).getFirst();
					for (int i = 0; i < sum.length; i++) {
						sum[i] = createAuxVar(sum[i]);
					}
					//	Term lhs = (encB != False);
					final Term lhs = mTheory.or(encB);
					final Term bvult =
							createAuxVar(mTheory.not(adder(remainder, negate(encB), mTheory.mTrue).getSecond()));
					for (int i = 0; i < conjunction.length; i++) {
						conjunction[i] = mTheory.and(
								mTheory.or(mTheory.not(sum[i]), encA[i]),
								mTheory.or(mTheory.not(encA[i]), sum[i]));
					}

					final Term divisionConstraint = mTheory.and(mTheory.or(mTheory.not(lhs), mTheory.and(conjunction)),
							mTheory.or(lhs, mTheory.not(mTheory.and(conjunction))));
					toClauses(divisionConstraint);

					final Term remainderConstraint = mTheory.and(mTheory.or(mTheory.not(lhs), bvult),
							mTheory.or(lhs, mTheory.not(bvult)));
					toClauses(remainderConstraint);
					return;

				default:
					throw new UnsupportedOperationException(
							"Unsupported functionsymbol for bitblasting: " + fsym.getName());
				}
				for (int i = 0; i < conjunction.length; i++) {
					toClauses(mTheory.or(mTheory.not(conjunction[i]), encTerm[i]));
					toClauses(mTheory.or(mTheory.not(encTerm[i]), conjunction[i]));
				}
			}
		} else {
			throw new UnsupportedOperationException("Unknown BVConstraint for term: " + term);
		}
	}

	// 00 concat 01 = 0001
	// as Array: [0 0] concat [1 0] = [1 0 0 0]
	private Term[] concatArrays(final Term[] b, final Term[] a) {
		final Term[] result = Arrays.copyOf(a, a.length + b.length);
		System.arraycopy(b, 0, result, a.length, b.length);
		return result;
	}

	// negates each term in terms array
	private Term[] negate(final Term[] terms) {
		final Term[] negateresult = new Term[terms.length];
		for (int i = 0; i < terms.length; i++) {
			negateresult[i] = mTheory.not(terms[i]);
		}
		return negateresult;
	}

	// returns a xor b xor cin in CNF
	private Term sumAdder(final Term a, final Term b, final Term cin) {
		if (cin.equals(mTheory.mFalse)) {
			return mTheory.and(mTheory.or(mTheory.not(a), mTheory.not(b)),
					mTheory.or(a, b));
		} else {
			return mTheory.and(mTheory.or(mTheory.not(a), mTheory.not(b), cin),
					mTheory.or(mTheory.not(a), b, mTheory.not(cin)),
					mTheory.or(a, mTheory.not(b), mTheory.not(cin)),
					mTheory.or(a, b, cin));
		}
	}

	// returns ((a and b) or (mTheory.(a xor b) and cin)) in CNF
	private Term carryAdder(final Term a, final Term b, final Term cin) {
		if (cin.equals(mTheory.mFalse)) {
			return mTheory.and(a, b);
		} else if (cin.equals(mTheory.mTrue)) {
			return mTheory.or(a, b);
		}
		return mTheory.and(mTheory.or(a, b), mTheory.or(a, cin), mTheory.or(b, cin));
	}

	private Term[] carryBits(final Term[] encA, final Term[] encB, final Term cin) {
		assert encA.length == encB.length;
		final Term[] carryBits = new Term[encA.length + 1];
		carryBits[0] = cin;
		for (int i = 1; i <= encA.length; i++) {
			carryBits[i] = carryAdder(encA[i - 1], encB[i - 1], carryBits[i - 1]);
		}
		return carryBits;
	}

	private Pair<Term[], Term> adder(final Term[] encA, final Term[] encB, final Term cin) {
		assert encA.length == encB.length;
		final Term[] sumResult = new Term[encA.length];
		final Term[] carryBits = carryBits(encA, encB, cin);
		for (int i = 0; i < encA.length; i++) {
			sumResult[i] = sumAdder(encA[i], encB[i], createAuxVar(carryBits[i]));
		}
		final Term cout = carryBits[carryBits.length - 1];
		return new Pair<>(sumResult, cout);
	}

	// create all auxiliary variables, needed to get rid of recursions
	private Term[][] createBoolVarMap(final int stage, final int indices) {
		final Term[][] boolvarmap = new Term[stage][indices];
		for (int s = 0; s < stage; s++) {
			for (int i = 0; i < indices; i++) {
				final String stageRec = "rec_" + i + "_" + s;
				final TermVariable boolVar = mTheory.createFreshTermVariable(stageRec, mTheory.getSort("Bool"));
				mBoolAtoms.put(boolVar, new BooleanVarAtom(boolVar, mStackLevel));
				boolvarmap[s][i] = boolVar;
			}
		}
		return boolvarmap;
	}


	// create all bool variables representing an bitvector
	private Term[] createBoolVarArray(final int indices) {
		final Term[] boolvarArray = new Term[indices];
		for (int i = 0; i < indices; i++) {
			final String stageRec = "aux_" + i;
			final TermVariable boolVar = mTheory.createFreshTermVariable(stageRec, mTheory.getSort("Bool"));
			mBoolAtoms.put(boolVar, new BooleanVarAtom(boolVar, mStackLevel));
			boolvarArray[i] = boolVar;
		}

		return boolvarArray;
	}

	/*
	 * Check if a aux var helps in the cnf process
	 * If (appterm.getParameters().length > 1), create auxvar and add it to cnf
	 * Else return input
	 */
	private Term createAuxVar(final Term represented) {
		if (represented instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) represented;
			if (appterm.getParameters().length > 1) { // Maybe only worth, if appterm is a conjunction
				final TermVariable boolVar = mTheory.createFreshTermVariable("AuxVar", mTheory.getSort("Bool"));
				mBoolAtoms.put(boolVar, new BooleanVarAtom(boolVar, mStackLevel));
				toClauses(mTheory.and(mTheory.or(mTheory.not(boolVar), represented),
						mTheory.or(mTheory.not(represented), boolVar)));
				return boolVar;
			}
		}
		//Probably not worth to add the Aux Var
		return represented;
	}


	/*
	 * Barrel Shifter
	 * Optimization: a<<b = ite(b3 \/ b4, (0,0,0,0), ls(a,b, log_2(length a) - 1))
	 * TODO Optimize, if encB True, and second case recommend DPLL to set auxVar to false
	 * leftshift, true if bvshl. False if bvlshr
	 */
	private Term[] shift(final Term a, final Term b, int stage, final boolean leftshift) {

		final Term[] encA = mEncTerms.get(a);
		final Term[] encB = mEncTerms.get(b);
		final Term[] shiftResult = new Term[encA.length];

		// Log Base 2, rounded up
		final int logTwo = (int) Math.ceil((float) (Math.log(encA.length) / Math.log(2)));
		final Term[][] boolvarmap = createBoolVarMap(logTwo, encA.length);
		// if any enB[x] with x > log_2(encA.length) is true, then shift result is zero BitVec
		for (int i = 0; i < encA.length; i++) {
			final List<Term> disj = new ArrayList<>();
			for (int k = logTwo; k < encB.length; k++) {
				disj.add(encB[k]);
			}
			final Term disjunction = listToDisjunction(disj, false);
			shiftResult[i] = mTheory.and(mTheory.or(mTheory.not(disjunction), mTheory.mFalse),
					mTheory.or(mTheory.or(disjunction), boolvarmap[logTwo - 1][i]));
		}
		// Only consider stages smaller than maximal shift distance
		stage = logTwo;
		for (int s = 0; s < stage; s++) {
			for (int i = 0; i < encA.length; i++) {
				final int pow = (int) Math.pow(2, s);
				final Term ifTerm;
				final Term elseTerm;
				Term thenTerm;
				if (s == 0) {
					ifTerm = encB[0];
					elseTerm = encA[i];
					// rightshift
					if ((i + pow < encA.length) && !leftshift) {
						thenTerm = encA[i + pow];
						// leftshift
					} else if (i >= pow && leftshift) {
						thenTerm = encA[i - pow];
						// no shift
					} else {
						thenTerm = mTheory.mFalse;
					}
					// ifthenelse in CNF (not a or b) and (a or c)
				} else {
					ifTerm = encB[s];
					elseTerm = boolvarmap[s - 1][i];
					if ((i + pow < encA.length) && !leftshift) {
						thenTerm = boolvarmap[s - 1][i + pow];
					} else if (i >= pow && leftshift) {
						thenTerm = boolvarmap[s - 1][i - pow];
					} else {
						thenTerm = mTheory.mFalse;
					}
				}
				// Add Auxiliary variables and their represented term (ifte), as clauses
				// Save in Set to prevent douplicats?
				toClausesIte(boolvarmap[s][i], ifTerm, elseTerm, thenTerm);
			}
		}
		return shiftResult;
	}

	/*
	 * get's a list of terms,
	 * returns these terms as disjunction
	 * if negated is set to true, each disjunct will be negated
	 * TODO: Doppel Negation vermeiden!! f�r code �bersicht
	 */
	private Term listToDisjunction(final List<Term> list, final boolean negate) {
		assert !list.isEmpty();
		Term[] disjArray = new Term[list.size()];
		disjArray = list.toArray(disjArray);
		for (int i = 0; i < list.size(); i++) {
			if (negate) {
				disjArray = negate(disjArray);
			}
		}
		return mTheory.or(disjArray);
	}

	/*
	 * Used, when b is not a term in the orginial formula, therefore mEncTerms.get(b) would be null
	 */
	private Term[] leftshiftMul(final Term[] encA, final String b, final int stage) {
		final Term[] shiftResult = new Term[encA.length];
		if (stage == -1) {
			return encA;
		} else {
			for (int i = 0; i < encA.length; i++) {
				if (b.charAt(b.length() - 1 - stage) == '1') {
					if (i >= Math.pow(2, stage)) {
						shiftResult[i] =
								leftshiftMul(encA, b, stage - 1)[i - (int) Math.pow(2, stage)];
					} else {
						shiftResult[i] = mTheory.mFalse;
					}
				} else {
					shiftResult[i] = leftshiftMul(encA, b, stage - 1)[i];
				}
			}
		}
		return shiftResult;
	}

	private Term[] multiplier(final Term a, final Term b, final int stage) {
		final Term[] encA = mEncTerms.get(a);
		final Term[] encB = mEncTerms.get(b);
		return multiplier(encA, encB, stage);
	}

	/*
	 * Multiplier withouth recursion. Instead we use aux vars.
	 * TODO test for bit vec width 1
	 */
	private Term[] multiplier(final Term[] encA, final Term[] encB, final int stage) {
		final int size = encA.length;
		final Term[] zeroVec = new Term[size];
		Arrays.fill(zeroVec, mTheory.mFalse);
		final Term[][] boolvarmap = createBoolVarMap(stage + 1, encA.length);
		if (stage == 0) {
			return zeroVec;
		}
		// Create AuxVars for each, except last.
		for (int s = 0; s < stage; s++) {
			final Term[] mul;
			final Term[] shift;
			if (s == 0) {
				mul = zeroVec;
				shift = encA;
			} else {
				// Auxiliary Variable
				mul = boolvarmap[s - 1];
				String SAsString = Integer.toString(s, 2);
				SAsString = new String(new char[size - SAsString.length()]).replace("\0", "0") + SAsString;
				shift = leftshiftMul(encA, SAsString, size - 1);
			}
			final Term[] ifte = new Term[size];
			for (int i = 0; i < size; i++) {
				if (encB[i].equals(mTheory.mTrue)) {
					ifte[i] = mTheory.or(mTheory.not(encB[s]), shift[i]);
				} else if (encB[i].equals(mTheory.mFalse)) {
					ifte[i] = mTheory.or(encB[s], mTheory.mFalse);
				}
				else {
					// mTheory.ifthenelse(encB[stage], shift[i], mTheory.mFalse);
					ifte[i] = mTheory.and(
							mTheory.or(mTheory.not(encB[s]), shift[i]),
							mTheory.or(encB[s], mTheory.mFalse));
				}
			}
			final Term[] sum = adder(mul, ifte, mTheory.mFalse).getFirst();
			for (int i = 0; i < size; i++) {
				// boolvarmap[s][i] <=> sum[i]
				toClauses(mTheory.and(mTheory.or(mTheory.not(boolvarmap[s][i]), sum[i]),
						mTheory.or(mTheory.not(sum[i]), boolvarmap[s][i])));
			}
		}
		// Last stage
		final Term[] shift;
		// stage must not be 0 at this point!
		String SAsString = Integer.toString(stage, 2);
		SAsString = new String(new char[size - SAsString.length()]).replace("\0", "0") + SAsString;
		shift = leftshiftMul(encA, SAsString, size - 1);

		final Term[] ifte = new Term[size];
		for (int i = 0; i < size; i++) {
			if (encB[i].equals(mTheory.mTrue)) {
				ifte[i] = mTheory.or(mTheory.not(encB[stage]), shift[i]);
			} else if (encB[i].equals(mTheory.mFalse)) {
				ifte[i] = mTheory.or(encB[stage], mTheory.mFalse);
			} else {
				// mTheory.ifthenelse(encB[stage], shift[i], mTheory.mFalse);
				ifte[i] = mTheory.and(
						mTheory.or(mTheory.not(encB[stage]), shift[i]),
						mTheory.or(encB[stage], mTheory.mFalse));
			}
		}
		final Term[] sum = adder(boolvarmap[stage - 1], ifte, mTheory.mFalse).getFirst();
		return sum;
	}


	private void toClauses(final Term term) {
		final CleanTransfomer cleaner = new CleanTransfomer();
		final NnfTransformer nnf = new NnfTransformer();
		final Term nnfTerm = nnf.transform(term);
		final CnfTransformer cnf = new CnfTransformer();
		final Term cnfTerm = cnf.transform(cnf.transform(nnfTerm));
		final Term cleanTerm = cleaner.transform(cnfTerm);
		if (cleanTerm instanceof ApplicationTerm) {
			final ApplicationTerm appClean = (ApplicationTerm) cleanTerm;
			if (appClean.getFunction().getName().equals("and")) {
				for (int i = 0; i < appClean.getParameters().length; i++) {
					addClauses(appClean.getParameters()[i]);
				}
			}
		} else {
			addClauses(cleanTerm);
		}
	}


	/*
	 * atom <=> ite into cnf
	 * Add Clauses of (boolVar <=> ifte) to dpll
	 * ifte arguments need to be literals
	 */
	private void toClausesIte(final Term atom, final Term ifTerm, final Term elseTerm, final Term thenTerm) {
		final Literal atomlit = getLiteral(atom);
		final Literal ifLit = getLiteral(ifTerm);
		final Literal elseLit = getLiteral(elseTerm);
		final Literal thenLit = getLiteral(thenTerm);
		if (!thenTerm.equals(mTheory.mFalse)) {
			final Literal[] lit1 = { atomlit, ifLit.negate(), thenLit.negate() };
			addClause(lit1);
			final Literal[] lit2 = { atomlit.negate(), ifLit, elseLit };
			addClause(lit2);
			final Literal[] lit3 = { atomlit.negate(), ifLit.negate(), thenLit };
			addClause(lit3);
			final Literal[] lit4 = { atomlit, elseLit.negate(), elseLit };
			addClause(lit4);
		} else {
			// thenTerm = mTheory.mFalse;
			final Literal[] lit1 = { atomlit.negate(), ifLit, elseLit };
			addClause(lit1);
			final Literal[] lit2 = { atomlit.negate(), ifLit.negate() };
			addClause(lit2);
		}
		final Literal[] lit5 = { atomlit, ifLit.negate(), ifLit };
		addClause(lit5);
		final Literal[] lit6 = { atomlit, ifLit, elseLit.negate() };
		addClause(lit6);
	}

	private Literal getLiteral(final Term term) {
		if(term instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) term;
			final FunctionSymbol fsym = appterm.getFunction();
			if (fsym.getName().equals("not")) {
				return mBoolAtoms.get(appterm.getParameters()[0]).negate();
			}
		}
		return mBoolAtoms.get(term);
	}

	private void addClause(final Literal[] literals) {
		final Clause cl = new Clause(literals, mStackLevel);
		cl.setProof(new LeafNode(-1, SourceAnnotation.EMPTY_SOURCE_ANNOT));
		mClauses.add(cl);
	}

	/*
	 * term must be a disjunction or literal
	 */
	private void addClauses(final Term term) {
		final ArrayList<Literal> literals = new ArrayList<>();
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appterm = (ApplicationTerm) term;
			final FunctionSymbol fsym = appterm.getFunction();
			if (fsym.getName().equals("or")) {
				for (int i = 0; i < appterm.getParameters().length; i++) {
					literals.add(getLiteral(appterm.getParameters()[i]));
				}
			} else if (fsym.getName().equals("true")) {
				literals.add(new TrueAtom());
			} else {
				literals.add(getLiteral(term));
			}
		} else {
			literals.add(getLiteral(term));
		}
		final Clause cl = new Clause(literals.toArray(new Literal[literals.size()]), mStackLevel);
		cl.setProof(new LeafNode(-1, SourceAnnotation.EMPTY_SOURCE_ANNOT));
		mClauses.add(cl);
	}

	public Collection<DPLLAtom> getBoolAtoms() {
		return mBoolAtoms.values();
	}

	public ScopedArrayList<Clause> getClauses() {
		return mClauses;
	}

	public Literal[] getNegatedInputLiterals() {
		final Literal[] lit = new Literal[mInputLiterals.size()];
		for (int i = 0; i < mInputLiterals.size(); i++) {
			lit[i] = mInputLiterals.get(i).negate();
		}
		return lit;
	}

	public HashMap<Term, Literal> getLiteralMap() {
		return mLiterals;
	}
}
