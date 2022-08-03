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
import java.util.HashSet;
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.ScopedArrayList;

/**
 * Class implementing a XOR-reasoning module.
 *
 * to be continued..
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
	/** Column number of a Literal */
	LinkedHashMap<DPLLAtom, Integer> mPosition;
	/**
	 * Atoms that are already built, position in BitSet is 1 for every variable
	 * involved in XorAtom
	 */
	LinkedHashMap<BitSet, XorAtom> mBuiltAtoms;
	/**
	 * List of literals ready for propagation. Using a Queue (FIFO-List) as this
	 * data structure is also used in LinArSolve
	 */
	final Queue<Literal> mProplist;

	/**
	 * The Tableau
	 */
	ScopedArrayList<TableauRow> mTableau;
	/**
	 * List of Variable Infos for every variable. the variableInfo in
	 * mVariableInfos[i] belongs to the variable on position i (i.e. with key i in
	 * mPosition)
	 */
	ArrayList<VariableInfo> mVariableInfos;

	private final Set<DPLLAtom> mVariableSet;

	public XorTheory(final Clausifier clausifier) {
		mClausifier = clausifier;
		mNumberOfRows = 0;
		mNumberOfVars = 0;
		mPosition = new LinkedHashMap<>();
		mBuiltAtoms = new LinkedHashMap<>();
		mProplist = new ArrayDeque<>();

		mTableau = new ScopedArrayList<TableauRow>();
		mVariableInfos = new ArrayList<VariableInfo>();
		mVariableSet = new HashSet<DPLLAtom>();

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
		// TODO: setting VariableInfo should maybe be its own function
		final VariableInfo info = new VariableInfo(xorPosition, true, xorAtom, mTableau.size());

		assert xorPosition == mVariableInfos.size();
		mVariableInfos.add(info);

		final BitSet newTableauRowBitSet = (BitSet) entries.clone();
		// nach dem Klonen: BitSet durchlaufen. checken für jedes gesetzte Bit ob es
		// eine Zeilenvariable ist
		// Wenn ja entries mit der betreffenden Zeile xor-en. so kommt die Variable
		// wieder raus aus dem Bitset

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
		mTableau.add(newTableauRow);
		mVariableInfos.set(xorPosition, info);
		return xorAtom;
	}

	@Override
	public Clause startCheck() {
		// momentan nicht wichtig
		return null;
	}

	@Override
	public void endCheck() {
		// momentan nicht wichtig
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
		// position of literal is set, i.e. 1)

		// if the set variable is a row variable, we mark the row as dirty to propagate
		// later
		if (setAtomInfo.IsRow()) {
			// markiere Zeile als dirty
			final TableauRow row = mTableau.get(setAtomRowNumber);
			row.mIsDirty = true;
		} else {
			// if the set variable is a column variable, we decrement the counter for all
			// rows in which the set variable appears and check for conflicts
			for (final TableauRow row : mTableau) {
				final BitSet setAtomTableauRowEntries = row.getmEntries();
				if (setAtomTableauRowEntries.get(setAtomPosition)) {
					row.decrementUnassigned();

					if (row.getNumUnassigned() == 0) {
						return checkForPropagationOrConflict(row); // ?
					}
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
	 * @return
	 *
	 *         TODO Test
	 */
	public Clause checkForPropagationOrConflict(final TableauRow row) {
		final BitSet entries = row.getmEntries();
		final DPLLAtom rowVariable = row.mRowVar.mAtom;
		final Boolean result = false;

		for (int i = entries.nextSetBit(0); i >= 0; i = entries.nextSetBit(i + 1)) {
			final VariableInfo varInfo = mVariableInfos.get(i);
			final DPLLAtom variableAtom = varInfo.mAtom;
			final Boolean assignment = variableAtom.getDecideStatus().getSign() > 0;
			// calculate result (value that the row variable should have)
			Boolean.logicalXor(result, assignment);
		}
		// if the row variable is not decided yet (DecideStatus() == null), we add it to
		// the propagation list mProplist to propagate later in checkpoint()
		if (rowVariable.getAtom().getDecideStatus() == null && !mProplist.contains(rowVariable)) {
			mProplist.add(rowVariable);
		}
		// conflict: if the result does not equal the assigned value for the row
		// variable, we return a conflict clause
		if (rowVariable.getAtom().getDecideStatus().getSign() > 0 != result) {
			return getUnitClause(rowVariable.getAtom());
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
			// if the variable to be backtracked is a column var, we need to update
			// mNumUnassignedColumnVars for each row where the variable to be backtracked
			// occurs.
			for (final TableauRow row: mTableau) {
				final BitSet entries = row.getmEntries();
				if (entries.get(positionToBacktrack)) {
					row.incrementUnassigned();
				}
			}

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
				assert columnVarPosition != -1;

				swap(row.mRowVar.mColumnNumber, columnVarPosition);

				row.mIsDirty = false;

			}
		}
		// check for conflicts and propagations
		for (final TableauRow row : mTableau) {
			if (row.getNumUnassigned() == 0) { // we are ready for checking for conflicts or propagations
				final Clause conflictClause = checkForPropagationOrConflict(row);
				if (conflictClause != null) {
					return conflictClause;
				}
			}
		}
		return null;
	}

	/***
	 * This function swaps two variables. the parameter rowVar becomes a column
	 * Variable and the parameter columnVar becomes the new row variable.
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


		// walk through rows of the tableau. if the column variable occurs, we xor that
		// row with the pivot row
		for (final TableauRow row : mTableau) {
			final BitSet entries = row.getmEntries();
			if (entries.get(columnVar) && row != pivotRow) {
				entries.xor(pivotRow.getmEntries());
				// counter updaten
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
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Literal getPropagatedLiteral() {
		/**
		 * Check if mPropList is empty, if not return first element
		 */
		if (!mProplist.isEmpty()) {
			return mProplist.remove();
		} else {
			return null;
		}
	}

	@Override
	public Clause getUnitClause(final Literal literal) {

		final ArrayList<Literal> conflictClause = new ArrayList<Literal>();
		final int literalPosition = mPosition.get(literal);
		final VariableInfo literalInfo = mVariableInfos.get(literalPosition);
		final int rowNumber = literalInfo.mRowNumber;
		final TableauRow row = mTableau.get(rowNumber);
		final BitSet entries = row.getmEntries();

		// go through set entries of the row of the literal given as parameter
		// get the literal corresponding to the set bit, negate it and add it to the
		// conflict clause
		for (int i = entries.nextSetBit(0); i >= 0; i = entries.nextSetBit(i + 1)) {
			// skip row variable (xor literal)
			if (i != literalPosition) {
				final DPLLAtom explanationAtom = mVariableInfos.get(i).mAtom;
				final Literal explanationLiteral = explanationAtom.getDecideStatus().negate();
				conflictClause.add(explanationLiteral);
			}
		}
		conflictClause.add(literal);

		final Clause explanationClause = new Clause(conflictClause.toArray(new Literal[conflictClause.size()]));
		return explanationClause;
	}

	@Override
	public Literal getSuggestion() {
		// momentan nicht wichtig
		return null;
	}

	@Override
	public int checkCompleteness() {
		return DPLLEngine.COMPLETE;
	}

	@Override
	public void printStatistics(final LogProxy logger) {
		// TODO Auto-generated method stub
		// wie viel zeit gebraucht zum pivoten
	}

	@Override
	public void dumpModel(final LogProxy logger) {
		// TODO Auto-generated method stub
		// debugging funktion
	}

	@Override
	public void increasedDecideLevel(final int currentDecideLevel) {
		// momentan nicht wichtig

	}

	@Override
	public void decreasedDecideLevel(final int currentDecideLevel) {
		// momentan nicht wichtig
	}



	@Override
	public Clause backtrackComplete() {
		return null;
	}

	@Override
	public void backtrackAll() {
		// momentan nicht wichtig

	}

	@Override
	public void restart(final int iteration) {
		// momentan nicht wichtig

	}

	@Override
	public void removeAtom(final DPLLAtom atom) {
		final int position = mPosition.get(atom);
		// remove all rows where atom occurs
		for (final TableauRow row : mTableau) {
			final BitSet entries = row.getmEntries();
			if (entries.get(position)) {
				mTableau.remove(row);
			}
		}
	}

	@Override
	public void push() {
		// siehe LA Theorie.
		// startscope bei allen ScopedArrayLists
		// -------------------------------------------------------------------------
		// Frage dazu: Soll außer das Tableau noch was anderes ScopedArrayList sein?
		// -------------------------------------------------------------------------
		// merken, wie viele Zeilen man hat
		mTableau.beginScope();

	}

	@Override
	public void pop() {
		// siehe LA Theorie
		// endscope bei allen ScopedArrayLists
		// gelöschte Variablen durchgehen.
		// ---------------------------------------------------------------------------
		// Frage dazu: manche Variablen, die in der Tableau-Reihe einen Eintrag hat,
		// kommen ja auch in anderen Reihen vor. Es wäre doch zu mühsam, für jede
		// Variable, die in einer zu löschenden Reihe vorkommt, zu checken ob sie nicht
		// doch irgendwo anders vorkommt bevor man die legal löschen darf. Die
		// row-variable kann man löschen, die kommt ja eh nur einmal im Tableau vor.
		// ---------------------------------------------------------------------------
		// Zustand vor dem zugehörigen push wiederherstellen
		TableauRow rowToDelete;
		BitSet entriesToDelete;
		VariableInfo rowVarToDeleteInfo;
		int rowVarToDeletePosition;
		DPLLAtom rowVarAtom;
		final int prevVarNum = mTableau.getLastScopeSize();
		// for every new Tableau row since last push:
		for (int i = mTableau.size() - 1; i >= prevVarNum; i--) {
			rowToDelete = mTableau.get(i);
			rowVarToDeleteInfo = rowToDelete.mRowVar;
			rowVarAtom = rowVarToDeleteInfo.mAtom;

			rowVarToDeletePosition = mPosition.get(rowVarAtom);
			// remove row var from mVariableInfos
			mVariableInfos.remove(rowVarToDeletePosition);
			// remove row var from mPosition
			mPosition.remove(rowVarAtom);
			entriesToDelete = rowToDelete.getmEntries();
			// remove corresponding xor-Atom from mBuiltAtoms
			mBuiltAtoms.remove(entriesToDelete);

		}
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
}