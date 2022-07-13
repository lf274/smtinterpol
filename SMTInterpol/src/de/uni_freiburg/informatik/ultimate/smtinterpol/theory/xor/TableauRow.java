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
	 * mCounter counts the Variables in the TableauRow that are still unassigned
	 * TODO: unassinged COLUMN variables zählen. Dann wäre bei 0 propagieren,
	 * Konflikt ist wenn die Zeilenvariable einen Wert hat der nicht übereinstimmt
	 */
	private int mNumUnassigned;
	VariableInfo mRowVar;

	Boolean mIsDirty; // a row is dirty, if the row variable is set


	public TableauRow(final BitSet newRow, final int numUnassigned, final VariableInfo rowVar,
			final Set<DPLLAtom> dpllAtoms) {
		setmEntries(newRow);
		setNumUnassigned(numUnassigned);
		mRowVar = rowVar;
		mIsDirty = false;
	}


	public int getNumUnassigned() {
		return mNumUnassigned;
	}

	public void setNumUnassigned(final int mNumUnassigned) {
		this.mNumUnassigned = mNumUnassigned;
	}

	public BitSet getmEntries() {
		return mEntries;
	}

	public void setmEntries(final BitSet mEntries) {
		this.mEntries = mEntries;
	}

	/**
	 * Counts the unassigned variables
	 *
	 * @param numberOfRow
	 * @return
	 */
	public void decrementUnassigned() {
		mNumUnassigned -= 1;
	}
}