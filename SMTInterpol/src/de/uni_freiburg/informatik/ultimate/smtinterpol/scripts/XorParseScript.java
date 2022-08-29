package de.uni_freiburg.informatik.ultimate.smtinterpol.scripts;

import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;



public class XorParseScript extends LoggingScript {

	ArrayList<Term> mXorTermCandidates = new ArrayList<Term>();
	ArrayList<Term> mXorCandidateParameters = new ArrayList<Term>();

	Boolean mXorCandidateParity;

	public XorParseScript() throws IOException {
		this("Test.SMT2", true);
	}

	public XorParseScript(String file, boolean autoFlush) throws IOException {
		super(file, autoFlush);
		// TODO Auto-generated constructor stub
	}

	public XorParseScript(String file, boolean autoFlush, boolean useCSE) throws IOException {
		super(file, autoFlush, useCSE);
		// TODO Auto-generated constructor stub
	}

	public XorParseScript(Script script, String file, boolean autoFlush) throws IOException {
		super(script, file, autoFlush);
		// TODO Auto-generated constructor stub
	}

	public XorParseScript(Script script, String file, boolean autoFlush, boolean useCSE) throws IOException {
		super(script, file, autoFlush, useCSE);
		// TODO Auto-generated constructor stub
	}


	/*
	 * Form of XOR-Terms in .cnf:
	 *  -3 -2 -1
 	 *	0
     *	3 2 -1
     *	0
 	 *	-3 2 1
 	 * 	0
 	 *	3 -2 1
 	 *  0
	 */
	@Override
	public LBool assertTerm(final Term term) throws SMTLIBException {
		ApplicationTerm at = null;
		if (term instanceof ApplicationTerm) {
			at = (ApplicationTerm) term;
			if (at.getParameters().length != 3) {
				return super.assertTerm(term);
			} else {
				checkXorCandidate(at);
				return LBool.UNKNOWN;
			}
		}
		return super.assertTerm(term);
	}

	public ArrayList<Term> getParameters(Term term) {
		final ArrayList<Term> parameters = new ArrayList<Term>();
		final ArrayDeque<Term> todoStack = new ArrayDeque<>();

		if (term instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm) term;
			todoStack.addAll(Arrays.asList(at.getParameters()));
			while (!todoStack.isEmpty()) {
				final Term parameter = todoStack.pop();
				if (parameter instanceof ApplicationTerm) {
					final ApplicationTerm atParameter = (ApplicationTerm) parameter;
					if (atParameter.getFunction().getName().equals(SMTLIBConstants.NOT)) {
						// todoStack.addAll(Arrays.asList(at.getParameters()));
						parameters.add(atParameter.getParameters()[0]);
						continue;
					} else {
						parameters.add(parameter);
					}
				}
			}
		}
		return parameters;
	}

	public Boolean getParity(Term[] parameters) {
		Integer numPositiveTerms = 0;
		for (final Term term : parameters) {
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm at = (ApplicationTerm) term;

				if (at.getFunction().getName() != SMTLIBConstants.NOT) {
					numPositiveTerms += 1;
				}
			}
		}
		if (numPositiveTerms % 2 == 0) {
			return false;
		} else {
			return true;
		}
	}


	public void checkXorCandidate(ApplicationTerm term) {
		final ArrayList<Term> parameters = getParameters(term);
		// first line
		if (mXorTermCandidates.size() == 0) {
			mXorTermCandidates.add(term);
			mXorCandidateParameters = parameters;
			mXorCandidateParity = getParity(term.getParameters());
		}
		else if (mXorTermCandidates.size() < 4) {
			if (parameters.equals(mXorCandidateParameters) && getParity(term.getParameters()) == mXorCandidateParity) {
				mXorTermCandidates.add(term);
			} else {
				for (final Term t : mXorTermCandidates) {
					super.assertTerm(t);
				}
				mXorTermCandidates.clear();
				mXorCandidateParameters.clear();
				mXorTermCandidates.add(term);
				mXorCandidateParameters = parameters;
				mXorCandidateParity = getParity(term.getParameters());
			}
		}
		if (mXorTermCandidates.size() == 4) {
			//
			final Term xorTerm = term(SMTLIBConstants.XOR, mXorCandidateParameters.get(0),
					mXorCandidateParameters.get(1), mXorCandidateParameters.get(2));
			mXorTermCandidates.clear();
			mXorCandidateParameters.clear();
			if (!mXorCandidateParity) {
				final Term result = term(SMTLIBConstants.NOT, xorTerm);
				super.assertTerm(result);
			} else {
				super.assertTerm(xorTerm);
			}
		}
	}

}

