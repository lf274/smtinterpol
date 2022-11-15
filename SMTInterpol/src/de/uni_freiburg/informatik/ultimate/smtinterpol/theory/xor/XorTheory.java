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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.LinkedHashMap;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.Clausifier;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLAtom;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.DPLLEngine;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.ITheory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.LeafNode;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ScopedArrayList;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ScopedHashMap;

/**
 * Class implementing a XOR Theory.
 *
 * Implements a method of Xor-reasoning as described in "Extending Clause
 * Learning SAT Solvers with Complete Parity Reasoning" by Tero Laitinen, Tommi
 * Junttila, and Ilkka Niemelä as well as " When Boolean Satisfiability Meets
 * Gaussian Elimination in a Simplex Way" by Cheng-Shen Han & Jie-Hong Roland
 * Jiang
 *
 * To build the Tableau, we construct for each Xor-Term an Xor-Variable, that
 * represents the xor of the non-basic (column) variables, the Xor-Variable will
 * be our basic (row) variable.
 *
 * When all the column-Variables are set, we compute the value of the row
 * variable and propagate the resulting value to the DPLL-Engine. For this, the
 * row variable may never be set if column variables are still unset. Also, a
 * row variable occurs only once in the Tableau.
 *
 *
 * @author Lena Funk
 */

public class XorTheory implements ITheory {
	/** The Clausifier. */
	final Clausifier mClausifier;
	/** Number of rows in tableau */
	final int mNumberOfRows;
	/** Number of variables */
	int mNumberOfVars;
	/** Column number of a Literal. */
	LinkedHashMap<DPLLAtom, Integer> mPosition;
	/**
	 * Atoms that are already built, position in BitSet is 1 for every variable
	 * involved in XorAtom.
	 */
	LinkedHashMap<BitSet, XorAtom> mBuiltAtoms;
	/**
	 * List of literals ready for propagation. Using a Queue (FIFO-List) as this
	 * data structure is also used in LinArSolve
	 */
	final Queue<Literal> mProplist;

	/**
	 * The Tableau rows
	 */
	ScopedArrayList<TableauRow> mTableau;

	/**
	 * The Tableau columns
	 */
	ScopedHashMap<Integer, BitSet> mTableauColumns;
	/**
	 * List of Variable Infos for every variable. the variableInfo in
	 * mVariableInfos[i] belongs to the variable on position i (i.e. with key i in
	 * mPosition)
	 */
	ScopedArrayList<VariableInfo> mVariableInfos;


	public XorTheory(final Clausifier clausifier) {
		mClausifier = clausifier;
		mNumberOfRows = 0;
		mNumberOfVars = 0;
		mPosition = new LinkedHashMap<>();
		mBuiltAtoms = new LinkedHashMap<>();
		mProplist = new ArrayDeque<>();

		mTableau = new ScopedArrayList<TableauRow>();
		//
		mTableauColumns = new ScopedHashMap<Integer, BitSet>();
		//
		mVariableInfos = new ScopedArrayList<VariableInfo>();

	}


	public Literal buildXorLiteral(final Set<DPLLAtom> variables) {
		// create term
		final Term[] smtAtoms = new Term[variables.size()];
		final Theory theory = mClausifier.getTheory();

		int offset = 0;
		int numUnassigned = 0;
		final BitSet entries = new BitSet();
		// build TableauRow entries
		for (final DPLLAtom atom: variables) {
			smtAtoms[offset++] = atom.getSMTFormula(theory);
			Integer position = mPosition.get(atom);
			// add new variables to mPosition and set VariableInfo
			if (position == null) {
				position = mPosition.size();
				mPosition.put(atom, position);

				final VariableInfo info = new VariableInfo(position, false, atom, -1);
				assert position == mVariableInfos.size();
				mVariableInfos.add(info);
				mNumberOfVars += 1;
			}
			if (atom.getDecideStatus() == null) {
				// numUnassigned only counts column variables
				numUnassigned++;
			}
			entries.set(position);
		}

		// check if we already built this xorAtom
		XorAtom xorAtom = mBuiltAtoms.get(entries);
		if (xorAtom != null) {
			return xorAtom;
		}

		// build the new xorAtom
		final Term xorTerm = theory.term(SMTLIBConstants.XOR, smtAtoms);
		// xorAtom is the row variable
		xorAtom = new XorAtom(null, xorTerm, xorTerm.hashCode(), mClausifier.getStackLevel());
		mClausifier.getEngine().addAtom(xorAtom);
		mBuiltAtoms.put(entries, xorAtom);
		final int xorPosition = mPosition.size();
		mPosition.put(xorAtom, xorPosition);


		final VariableInfo info = new VariableInfo(xorPosition, true, xorAtom, mTableau.size());

		assert xorPosition == mVariableInfos.size();
		mVariableInfos.add(info);

		final BitSet newTableauRowBitSet = (BitSet) entries.clone();

		// check if a column variable that is set in newTableauRowBitSet occurs
		// elsewhere in the tableau as a row variable.
		// if this is the case xor newTableauRowBitSet with that row

		BitSet row = new BitSet();
		for (int i = 0; i < newTableauRowBitSet.length(); ++i) {
			if (newTableauRowBitSet.get(i)) {
				final VariableInfo rowVarCandidateInfo = mVariableInfos.get(i);
				if (rowVarCandidateInfo.IsRow()) {
					final TableauRow rowVarCandidateInfoRow = mTableau.get(rowVarCandidateInfo.mRowNumber);
					row = rowVarCandidateInfoRow.getmEntries();
					newTableauRowBitSet.xor(row);
				}
			}
		}

		newTableauRowBitSet.set(xorPosition);
		final TableauRow newTableauRow = new TableauRow(newTableauRowBitSet, numUnassigned, info, variables);
		newTableauRow.calculateUnassigned(this);
		mTableau.add(newTableauRow);

		mVariableInfos.set(xorPosition, info);

		// add to tableau columns
		for (int i = newTableauRowBitSet.nextSetBit(0); i >= 0; i = newTableauRowBitSet.nextSetBit(i + 1)) {
			if (!mTableauColumns.containsKey(i)) {
				final BitSet column = new BitSet();
				mTableauColumns.put(i, column);
			}
			mTableauColumns.get(i).set(info.mRowNumber);
		}
		return xorAtom;
	}

	@Override
	public Clause startCheck() {
		return null;
	}

	@Override
	public void endCheck() {
	}


	@Override
	public Clause setLiteral(final Literal literal) {

		// literal has been set to true
		final DPLLAtom setAtom = literal.getAtom();
		final Integer setAtomPosition = mPosition.get(setAtom);

		// not our literal
		if (setAtomPosition == null) {
			return null;
		}
		final VariableInfo setAtomInfo = mVariableInfos.get(setAtomPosition);
		final int setAtomRowNumber = setAtomInfo.mRowNumber;
		// recalculate counter of corresponding tableau rows (every row where the
		// position of literal is set, i.e. 1), if the set literal is not a row variable

		// if the set variable is a row variable, we mark the row as dirty to propagate
		// later
		if (setAtomInfo.IsRow()) {
			// markiere Zeile als dirty
			final TableauRow row = mTableau.get(setAtomRowNumber);
			row.mIsDirty = true;
		} else {
			Clause potentialConflictClause = null;

			// get corresponding column
			final BitSet setAtomColumn = mTableauColumns.get(setAtomPosition);

			// walk through the set bits of the column. when a bit is set, then we have to
			// decrement the number of unassigned variables
			for (int i = setAtomColumn.nextSetBit(0); i >= 0; i = setAtomColumn.nextSetBit(i + 1)) {
				final TableauRow row = mTableau.get(i);

				row.calculateUnassigned(this);

				if (row.getNumUnassigned() == 0) {
					potentialConflictClause = checkForPropagationOrConflict(row);
				}
				if (potentialConflictClause != null) {
					return potentialConflictClause;
				}
			}
		}
		return null;
	}

	/**
	 * This Function is called when all column variables are assigned. In this
	 * function, the value of the row variable of the row given as parameter is
	 * calculated. Then, if we have no conflict, the row variable is added to the
	 * propagation list to be propagated later in checkpoint(). If we have a
	 * conflict, we return the conflict clause
	 *
	 * @param row
	 * @return conflict clause or null
	 *
	 *
	 */
	public Clause checkForPropagationOrConflict(final TableauRow row) {
		final BitSet entries = row.getmEntries();
		final DPLLAtom rowVariable = row.mRowVar.mAtom;
		boolean result = false;

		assert row.getNumUnassigned() == 0;

		for (int i = entries.nextSetBit(0); i >= 0; i = entries.nextSetBit(i + 1)) {
			if (i != row.mRowVar.mColumnNumber) {
				final VariableInfo varInfo = mVariableInfos.get(i);
				final DPLLAtom variableAtom = varInfo.mAtom;

				// calculate result (value that the row variable should have)
				// only calculate with variables that actually have a decide status
				assert variableAtom.getDecideStatus() != null;
				final Boolean assignment = variableAtom.getDecideStatus().getSign() > 0;
				result = result ^ assignment;

			}
		}
		Literal resultLiteral;
		if (result == false) {
			resultLiteral = rowVariable.negate();
		} else {
			resultLiteral = rowVariable;
		}
		// if the row variable is not decided yet (DecideStatus() == null), we add it to
		// the propagation list mProplist to propagate later in checkpoint()
		// change !mProplist.contains(rowVariable) to !mProplist.contains(res)
		if (rowVariable.getDecideStatus() == null && !mProplist.contains(rowVariable)
				&& !mProplist.contains(resultLiteral)) {
			mProplist.add(resultLiteral);
		}
		// conflict: if the result does not equal the assigned value for the row
		// variable, we return a conflict clause

		if (rowVariable.getDecideStatus() != null && rowVariable.getDecideStatus().getSign() > 0 != result) {
			assert (row.getNumUnassigned() == 0);
			return getUnitClause(resultLiteral);
		}
		return null;
	}


	@Override
	public void backtrackLiteral(final Literal literal) {
		final DPLLAtom atomToBacktrack = literal.getAtom();
		final Integer positionToBacktrack = mPosition.get(atomToBacktrack);

		if (positionToBacktrack == null) {
			return;
		}

		final VariableInfo varInfoToBacktrackInfo = mVariableInfos.get(positionToBacktrack);

		if (!varInfoToBacktrackInfo.IsRow()) {
			final BitSet columnToBacktrack = mTableauColumns.get(positionToBacktrack);
			for (int i = columnToBacktrack.nextSetBit(0); i >= 0; i = columnToBacktrack.nextSetBit(i + 1)) {
				final TableauRow row = mTableau.get(i);
				final BitSet entries = row.getmEntries();
				if (entries.get(positionToBacktrack)) {
					row.incrementUnassigned();
				}
			}

		} else {
			final int i = varInfoToBacktrackInfo.mRowNumber;
			final TableauRow row = mTableau.get(i);
			row.mIsDirty = false;
		}
	}


	@Override
	public Clause checkpoint() {
		for (final TableauRow row : mTableau) {
			if (row.mIsDirty) {
				// choose column variable to swap with row variable: the first unassigned column
				// variable
				final int columnVarPosition = findUnassingedVarToSwap(row.mRowVar.mRowNumber);

				// if this is the case, there are no unassigned variables in this row.
				// assert columnVarPosition != -1;

				if (columnVarPosition == -1) {
					break;
				}

				swap(row.mRowVar.mColumnNumber, columnVarPosition);

				row.mIsDirty = false;

			}
		}
		// check for conflicts and propagations
		for (final TableauRow row : mTableau) {
			if (row.getNumUnassigned() == 0) {
				// we are ready for checking for conflicts or propagations
				final Clause conflictClause = checkForPropagationOrConflict(row);
				if (conflictClause != null) {
					return conflictClause;
				}
			}
		}
		return null;
	}

	/***
	 * This function swaps a row variable with a column variables. the argument
	 * rowVar becomes a column Variable and the argument columnVar becomes the new
	 * row variable.
	 *
	 * The columnVar must be unassigned.
	 *
	 *
	 *
	 * @param rowVar
	 * @param columnVar
	 */
	public void swap(final int rowVar, final int columnVar) {
		final VariableInfo rowVarInfo = mVariableInfos.get(rowVar);
		final VariableInfo columnVarInfo = mVariableInfos.get(columnVar);
		final TableauRow pivotRow = mTableau.get(rowVarInfo.mRowNumber);

		final BitSet column = mTableauColumns.get(columnVar);

		for (int i = column.nextSetBit(0); i >= 0; i = column.nextSetBit(i + 1)) {
			final TableauRow row = mTableau.get(i);
			final Integer rowNumber = row.mRowVar.mRowNumber;
			final BitSet entries = row.getmEntries();
			if (row != pivotRow && entries.get(columnVar)) {
				entries.xor(pivotRow.getmEntries());
				row.calculateUnassigned(this);
				for (int j = 0; j < entries.length(); ++j) {
					if (entries.get(j)) {
						mTableauColumns.get(j).set(rowNumber);
					} else {
						mTableauColumns.get(j).clear(rowNumber);
					}
				}

			}
		}

		// in the pivot row, the assigned row variable is now a column variable
		// therefore we need to decrement the unassigned column variables for our pivot
		// row.
		pivotRow.decrementUnassigned();


		// set the column variable given as argument as the new row variable for the
		// pivot row
		pivotRow.mRowVar = columnVarInfo;
		columnVarInfo.mRowNumber = rowVarInfo.mRowNumber;
		// set row variable as column variable
		rowVarInfo.mRowNumber = -1;
	}


	public int findUnassingedVarToSwap(final int rowNumber) {
		final TableauRow row = mTableau.get(rowNumber);
		for (int i = row.getmEntries().nextSetBit(0); i >= 0; i = row.getmEntries().nextSetBit(i + 1)) {
			final VariableInfo variableInfo = mVariableInfos.get(i);
			if (variableInfo.mAtom.getDecideStatus() == null) {
				return i;
			}
		}
		return -1;
	}

	@Override
	public Clause computeConflictClause() {
		// final check
		return null;
	}

	@Override
	public Literal getPropagatedLiteral() {
		if (!mProplist.isEmpty()) {
			return mProplist.remove();
		} else {
			return null;
		}
	}

	@Override
	public Clause getUnitClause(final Literal literal) {

		final ArrayList<Literal> conflictClause = new ArrayList<Literal>();
		final int literalPosition = mPosition.get(literal.getAtom());
		final VariableInfo literalInfo = mVariableInfos.get(literalPosition);
		final int rowNumber = literalInfo.mRowNumber;
		final TableauRow row = mTableau.get(rowNumber);
		final BitSet entries = row.getmEntries();

		// go through set entries of the row of the literal given as parameter
		// get the literal corresponding to the set bit, negate it and add it to the
		// conflict clause

		assert (row.getNumUnassigned() == 0);
		for (int i = entries.nextSetBit(0); i >= 0; i = entries.nextSetBit(i + 1)) {
			// skip row variable (xor literal)
			if (i != literalPosition) {
				// assert (row.getNumUnassigned() == 0);
				final DPLLAtom explanationAtom = mVariableInfos.get(i).mAtom;
				// assert (row.getNumUnassigned() == 0);
				final Literal explanationLiteral = explanationAtom.getDecideStatus().negate();
				conflictClause.add(explanationLiteral);
			}
		}
		conflictClause.add(literal);

		final Clause explanationClause = new Clause(conflictClause.toArray(new Literal[conflictClause.size()]),
				new LeafNode(LeafNode.THEORY_XOR, XorAnnotation.XOR));
		return explanationClause;
	}

	@Override
	public Literal getSuggestion() {
		return null;
	}

	@Override
	public int checkCompleteness() {
		return DPLLEngine.COMPLETE;
	}

	@Override
	public void printStatistics(final LogProxy logger) {
	}

	@Override
	public void dumpModel(final LogProxy logger) {
	}

	@Override
	public void increasedDecideLevel(final int currentDecideLevel) {
	}

	@Override
	public void decreasedDecideLevel(final int currentDecideLevel) {
	}



	@Override
	public Clause backtrackComplete() {
		return null;
	}

	@Override
	public void backtrackAll() {
	}

	@Override
	public void restart(final int iteration) {
	}

	@Override
	public void removeAtom(final DPLLAtom atom) {
	}

	@Override
	public void push() {
		mTableau.beginScope();
		mVariableInfos.beginScope();

	}

	@Override
	public void pop() {
		TableauRow rowToDelete;
		BitSet entriesToDelete;
		VariableInfo rowVarToDeleteInfo;
		int rowVarToDeletePosition;
		DPLLAtom rowVarAtom;
		final int prevVarNum = mTableau.getLastScopeSize();
		final int lastScopeVarInfo = mVariableInfos.getLastScopeSize();
		// for every new Tableau row since last push:
		for (int i = mTableau.size() - 1; i >= prevVarNum; i--) {
			rowToDelete = mTableau.get(i);
			rowVarToDeleteInfo = rowToDelete.mRowVar;
			rowVarAtom = rowVarToDeleteInfo.mAtom;

			rowVarToDeletePosition = mPosition.get(rowVarAtom);
			entriesToDelete = rowToDelete.getmEntries();
			// remove corresponding xor-Atom from mBuiltAtoms
			mBuiltAtoms.remove(entriesToDelete);

		}
		for (int i = mVariableInfos.size() - 1; i >= lastScopeVarInfo; i--) {
			rowVarToDeleteInfo = mVariableInfos.get(i);
			mPosition.remove(rowVarToDeleteInfo.mAtom);

		}
		for (final BitSet column : mTableauColumns.values()) {
			column.clear(prevVarNum, column.length());

		}
		mTableau.endScope();
		mVariableInfos.endScope();
		mProplist.clear();
	}


	@Override
	public Object[] getStatistics() {
		return null;
	}

	@Override
	public void backtrackStart() {
		mProplist.clear();
	}

	public void checkCorrectCounter(TableauRow row) {
		int correctCounter = 0;
		final BitSet rowEntries = row.getmEntries();
		for (int i = rowEntries.nextSetBit(0); i >= 0; i = rowEntries.nextSetBit(i + 1)) {
			if (i != row.mRowVar.mColumnNumber) {
				final VariableInfo varInfo = mVariableInfos.get(i);
				final DPLLAtom variableAtom = varInfo.mAtom;

				if (variableAtom.getDecideStatus() == null) {
					correctCounter++;
				}
			}

		}
		assert (correctCounter == row.getNumUnassigned());
	}
}