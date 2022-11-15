/*
 * Copyright (C) 2009-2012 University of Freiburg
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

import java.util.BitSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;

/**
 * Data structure that stores a row of the linear arithmetic tableau to be used
 * by the XorTheory.
 *
 *
 *
 * @author Lena Funk
 */

public class TableauRow {
	/**
	 * mEntries represents one row in the Matrix. mEntries.get(index) returns 1 if
	 * the variable at position index is involved mEntries.get(index) returns 0 else
	 */
	private BitSet mEntries;

	/**
	 * mCounter counts the COLUMN Variables in the TableauRow that are still
	 * unassigned If mCounter is 0, its propagation time We have a conflict when
	 * rowVar != xor ( columnVars )
	 */
	private int mNumUnassignedColumnVars;

	VariableInfo mRowVar;

	Boolean mIsDirty; // a row is dirty, if the row variable is set

	// Set<DPLLAtom> mDpllAtoms;


	public TableauRow(final BitSet newRow, final int numUnassigned, final VariableInfo rowVar,
			final Set<DPLLAtom> dpllAtoms) {
		setmEntries(newRow);
		setNumUnassigned(numUnassigned);
		mRowVar = rowVar;
		mIsDirty = false;
		// mDpllAtoms = dpllAtoms;
	}


	public int getNumUnassigned() {
		return mNumUnassignedColumnVars;
	}

	public void setNumUnassigned(final int mNumUnassigned) {
		mNumUnassignedColumnVars = mNumUnassigned;
	}

	public BitSet getmEntries() {
		return mEntries;
	}

	public void setmEntries(final BitSet mEntries) {
		this.mEntries = mEntries;
	}

	/**
	 * Decrements the unassigned column variables.
	 *
	 * @param numberOfRow
	 * @return
	 */
	public void decrementUnassigned() {
		mNumUnassignedColumnVars -= 1;
	}

	/**
	 * Increments the unassigned column variables.
	 *
	 * @param numberOfRow
	 * @return
	 */
	public void incrementUnassigned() {
		mNumUnassignedColumnVars += 1;
	}

	public void calculateUnassigned(XorTheory xorTheory) {
		int correctCounter = 0;
		for (int i = mEntries.nextSetBit(0); i >= 0; i = mEntries.nextSetBit(i + 1)) {
			if (i != mRowVar.mColumnNumber) {
				final VariableInfo varInfo = xorTheory.mVariableInfos.get(i);
				final DPLLAtom variableAtom = varInfo.mAtom;

				if (variableAtom.getDecideStatus() == null) {
					correctCounter++;
				}
			}

		}
		mNumUnassignedColumnVars = correctCounter;
	}
}