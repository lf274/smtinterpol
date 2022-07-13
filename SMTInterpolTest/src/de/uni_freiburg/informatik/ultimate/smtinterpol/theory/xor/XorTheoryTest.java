package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.xor;

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
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol.ProofMode;

@RunWith(JUnit4.class)

public class XorTheoryTest {
	Theory mTheory;
	LogProxy mLogger;
	Clausifier mClausifier;
	DPLLEngine mDPLL;
	DPLLAtom[] mAtoms;
	XorTheory mXorTheory;


	public XorTheoryTest() {
		mTheory = new Theory(Logics.QF_UF);
		mLogger = new DefaultLogger();
		mLogger.setLoglevel(LogProxy.LOGLEVEL_DEBUG);
		mDPLL = new DPLLEngine(mLogger, () -> false);
		mClausifier = new Clausifier(mTheory, mDPLL, ProofMode.NONE);
		mClausifier.setLogic(Logics.QF_UF);
		mXorTheory = new XorTheory(mClausifier);
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
		final DPLLAtom atomA = new BooleanVarAtom(terma, 0);
		final DPLLAtom atomB = new BooleanVarAtom(termb, 0);
		final DPLLAtom atomC = new BooleanVarAtom(termc, 0);
		final DPLLAtom atomD = new BooleanVarAtom(termd, 0);
		mAtoms = new DPLLAtom[] { atomA, atomB, atomC, atomD };
	}

	@Test
	public void testCase1() {
		final LinkedHashSet<DPLLAtom> atomSet = new LinkedHashSet<DPLLAtom>(Arrays.asList(mAtoms));
		final Literal result = mXorTheory.buildXorLiteral(atomSet);
		Assert.assertTrue(result instanceof XorAtom);
		Assert.assertEquals("(xor a b c d)", result.getSMTFormula(mTheory).toString());
	}

	@Test
	public void testCase2() {
		final LinkedHashSet<DPLLAtom> atomSet1 = new LinkedHashSet<DPLLAtom>(Arrays.asList(mAtoms));
		final Literal result1 = mXorTheory.buildXorLiteral(atomSet1);
		final LinkedHashSet<DPLLAtom> atomSet2 = new LinkedHashSet<DPLLAtom>(
				Arrays.asList(mAtoms[3], mAtoms[2], mAtoms[1], mAtoms[0]));
		final Literal result2 = mXorTheory.buildXorLiteral(atomSet2);
		Assert.assertSame(result1, result2);
	}

	@Test
	public void testCase3() {

	}


}
