/*
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify it under
 * the terms of the GNU Lesser General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or (at your option) any
 * later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public License for more
 * details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol. If not, see <http://www.gnu.org/licenses/>.
 */

package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.xor;

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;

/**
 * Class implementing a XOR-Atom to be used with the XOR Theory
 *
 * To be continued..
 *
 * @author Lena Funk
 */

public class XorAtom extends DPLLAtom {
	/**
	 * still needs literals maybe
	 */
	private final String mName;
	private final Term mSmtFormula;
	private ArrayList<DPLLAtom> mVariables;

	public XorAtom(final String name, final Term smtFormula, final int hash, final int assertionstacklevel) {
		super(hash, assertionstacklevel);
		mName = name;
		mSmtFormula = smtFormula;
		setmVariables(new ArrayList<DPLLAtom>());
	}

	@Override
	public Term getSMTFormula(final Theory smtTheory) {
		return mSmtFormula;
	}

	@Override
	public String toString() {
		return mName;
	}

	public ArrayList<DPLLAtom> getmVariables() {
		return mVariables;
	}

	public void setmVariables(final ArrayList<DPLLAtom> mVariables) {
		this.mVariables = mVariables;
	}
}