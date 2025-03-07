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

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofRules;

/**
 * Annotations for Xor.
 *
 * These annotations have no data, so we can share them.
 *
 * @author Lena Funk
 *
 */
public final class XorAnnotation implements IAnnotation {
	/**
	 * The singleton EQAnnotation instance.
	 */
	public static final XorAnnotation XOR = new XorAnnotation();

	private final Annotation[] mAnnots = new Annotation[] { new Annotation(":XOR", null) };

	private XorAnnotation() {
	}

	@Override
	public Term toTerm(final Clause cls, final ProofRules proofRules) {
		return proofRules.oracle(cls.toProofLiterals(proofRules), mAnnots);
	}
}