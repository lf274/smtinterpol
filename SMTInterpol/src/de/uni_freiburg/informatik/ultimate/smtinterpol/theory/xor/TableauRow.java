package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.xor;

import java.util.BitSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;

/**
 * Data structure that stores a row of the linear arithmetic tableau to be used
 * by XorTheory.
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

	Set<DPLLAtom> mDpllAtoms;


	public TableauRow(final BitSet newRow, final int numUnassigned, final VariableInfo rowVar,
			final Set<DPLLAtom> dpllAtoms) {
		setmEntries(newRow);
		setNumUnassigned(numUnassigned);
		mRowVar = rowVar;
		mIsDirty = false;
		mDpllAtoms = dpllAtoms;
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

	public void calculateUnassigned() {
		mNumUnassignedColumnVars = 0;
		for (final DPLLAtom atom : mDpllAtoms) {
			if (atom != mRowVar.mAtom && atom.getDecideStatus() == null) {
				mNumUnassignedColumnVars += 1;
			}
		}
	}
}