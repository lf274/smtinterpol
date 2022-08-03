package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.xor;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.LinkedHashSet;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.JUnit4;

import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.DefaultLogger;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.BooleanVarAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ILiteral;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol.ProofMode;

@RunWith(JUnit4.class)

public class XorTheoryTest {
	Theory mTheory;
	LogProxy mLogger;
	Clausifier mClausifier;
	DPLLEngine mDPLL;
	DPLLAtom[] mAtoms1;
	DPLLAtom[] mAtoms2;
	XorTheory mXorTheory;
	Term mA, mB, mC;


	public XorTheoryTest() {
		mTheory = new Theory(Logics.QF_UF);
		mLogger = new DefaultLogger();
		mLogger.setLoglevel(LogProxy.LOGLEVEL_DEBUG);
		mDPLL = new DPLLEngine(mLogger, () -> false);
		mClausifier = new Clausifier(mTheory, mDPLL, ProofMode.NONE);
		mClausifier.setLogic(Logics.QF_UF);
		mXorTheory = mClausifier.getXorTheory();
		createAtoms();
	}

	private void createAtoms() {
		final Sort sort = mTheory.getSort(SMTLIBConstants.BOOL);
		mTheory.declareFunction("d", Script.EMPTY_SORT_ARRAY, sort);
		mTheory.declareFunction("c", Script.EMPTY_SORT_ARRAY, sort);
		mTheory.declareFunction("b", Script.EMPTY_SORT_ARRAY, sort);
		mTheory.declareFunction("a", Script.EMPTY_SORT_ARRAY, sort);
		final Term termd = mTheory.term("d");
		final Term termc = mTheory.term("c");
		final Term termb = mTheory.term("b");
		final Term terma = mTheory.term("a");
		mA = terma;
		mB = termb;
		mC = termc;
		final DPLLAtom atomA = new BooleanVarAtom(terma, 0);
		final DPLLAtom atomB = new BooleanVarAtom(termb, 0);
		final DPLLAtom atomC = new BooleanVarAtom(termc, 0);
		final DPLLAtom atomD = new BooleanVarAtom(termd, 0);
		mDPLL.addAtom(atomA);
		mDPLL.addAtom(atomB);
		mDPLL.addAtom(atomC);
		mDPLL.addAtom(atomD);
		mAtoms1 = new DPLLAtom[] { atomA, atomB, atomC, atomD };

		mTheory.declareFunction("e", Script.EMPTY_SORT_ARRAY, sort);
		mTheory.declareFunction("f", Script.EMPTY_SORT_ARRAY, sort);
		mTheory.declareFunction("g", Script.EMPTY_SORT_ARRAY, sort);
		mTheory.declareFunction("h", Script.EMPTY_SORT_ARRAY, sort);
		final Term terme = mTheory.term("e");
		final Term termf = mTheory.term("f");
		final Term termg = mTheory.term("g");
		final Term termh = mTheory.term("h");
		final DPLLAtom atomE = new BooleanVarAtom(terme, 0);
		final DPLLAtom atomF = new BooleanVarAtom(termf, 0);
		final DPLLAtom atomG = new BooleanVarAtom(termg, 0);
		final DPLLAtom atomH = new BooleanVarAtom(termh, 0);
		mDPLL.addAtom(atomE);
		mDPLL.addAtom(atomF);
		mDPLL.addAtom(atomG);
		mDPLL.addAtom(atomH);
		mAtoms2 = new DPLLAtom[] { atomA, atomB, atomC, atomD, atomE, atomF, atomG, atomH };
	}

	@Test
	public void testCase1() {
		final LinkedHashSet<DPLLAtom> atomSet = new LinkedHashSet<DPLLAtom>(Arrays.asList(mAtoms1));
		final Literal result = mXorTheory.buildXorLiteral(atomSet);
		Assert.assertTrue(result instanceof XorAtom);
		Assert.assertEquals("(xor a b c d)", result.getSMTFormula(mTheory).toString());
	}

	@Test
	public void testCase2() {
		final LinkedHashSet<DPLLAtom> atomSet1 = new LinkedHashSet<DPLLAtom>(Arrays.asList(mAtoms1));
		final Literal result1 = mXorTheory.buildXorLiteral(atomSet1);
		final LinkedHashSet<DPLLAtom> atomSet2 = new LinkedHashSet<DPLLAtom>(
				Arrays.asList(mAtoms1[3], mAtoms1[2], mAtoms1[1], mAtoms1[0]));
		final Literal result2 = mXorTheory.buildXorLiteral(atomSet2);
		Assert.assertSame(result1, result2);
	}

	@Test
	public void testCase3() {
		mDPLL.increaseDecideLevel();
		mDPLL.setLiteral(mAtoms1[0]);
		Assert.assertTrue((mAtoms1[0].getDecideStatus().getSign() > 0) == true);
	}

	@Test
	public void testCase4() {
//		mDPLL.setLiteral(mAtoms[0]);
//		mDPLL.setLiteral(mAtoms[1]);
//		mDPLL.setLiteral(mAtoms[2]);
//		mDPLL.setLiteral(mAtoms[3]);
		mDPLL.increaseDecideLevel();
		final LinkedHashSet<DPLLAtom> atomSet1 = new LinkedHashSet<DPLLAtom>(
				Arrays.asList(mAtoms2[0], mAtoms2[1], mAtoms2[2], mAtoms2[3]));
		final LinkedHashSet<DPLLAtom> atomSet2 = new LinkedHashSet<DPLLAtom>(
				Arrays.asList(mAtoms2[0], mAtoms2[5], mAtoms2[1], mAtoms2[6]));
		final Literal literal1 = mXorTheory.buildXorLiteral(atomSet1);
		mDPLL.setLiteral(literal1);
		// mXorTheory.setLiteral(literal1);
		final Literal literal2 = mXorTheory.buildXorLiteral(atomSet2);
		Assert.assertEquals(true, mXorTheory.mTableau.get(0).mIsDirty);
		mXorTheory.checkpoint();
		Assert.assertEquals(false, mXorTheory.mTableau.get(0).mIsDirty);
	}

	@Test
	public void testClausifier1() {
		final Term xorTerm = mTheory.term(SMTLIBConstants.XOR, mA, mB, mC);
		final ILiteral result = mClausifier.createLiteral(xorTerm, true, null);
		assertEquals(xorTerm, result.getSMTFormula(mTheory));
	}

	// verschachtelten Fall testen
	public void testClausifier2() {
		final Term negatedA = mTheory.not(mA);
		final Term xorTerm = mTheory.term(SMTLIBConstants.XOR, negatedA, mB, mC);

	}

}
