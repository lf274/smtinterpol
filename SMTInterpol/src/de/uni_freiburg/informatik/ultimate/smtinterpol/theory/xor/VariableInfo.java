/*
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */

package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.xor;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;

/**
 * Auxiliary class to represent needed information about a Variable.
 *
 * @author Lena Funk
 */

public class VariableInfo {
	/**
	 * Number of the column of a variable, corresponds to value of the variable in
	 * XorTheory.mPosition
	 */
	int mColumnNumber;
	/**
	 * Corresponding DPLL Atom
	 */
	DPLLAtom mAtom;
	/**
	 * Number of the row of a row variable. If the variable is NOT a row variable:
	 * mRowNumber = -1
	 */
	int mRowNumber;

	public VariableInfo(final int position, final boolean isNonBasic, final DPLLAtom atom, final int rowNumber) {
		mColumnNumber = position;
		mAtom = atom;
		mRowNumber = rowNumber;
	}

	/**
	 * Check whether a variable is a row variable
	 *
	 * @return <code>true</code> iff this variable is a row variable.
	 */
	public boolean IsRow() {
		if (mRowNumber != -1) {
			return true;
		} else {
			return false;
		}
	}
}