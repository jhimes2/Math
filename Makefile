.PHONY: all
all: Trigonometry/Trigonomtry.agdai ClassicalTopology/Topology.agdai NumberTheory/Finite.agdai NumberTheory/Integer.agdai Algebra/Matrix.agdai Algebra/Metric.agdai experiments.agdai

experiments.agdai: experiments.agda Data/Integer.agdai Data/Bool.agdai Data/Finite.agdai NumberTheory/Natural.agda
	agda $<

NumberTheory/Finite.agdai: NumberTheory/Finite.agda NumberTheory/Natural.agdai Data/Bool.agdai Data/Finite.agdai
	agda $<

NumberTheory/Integer.agdai: NumberTheory/Integer.agda NumberTheory/Natural.agdai
	agda $<

NumberTheory/Natural.agdai: NumberTheory/Natural.agda NumberTheory/Overloads.agdai
	agda $<

NumberTheory/Overloads.agdai: NumberTheory/Overloads.agda Data/Natural.agdai
	agda $<

Trigonometry/Trigonomtry.agdai: Trigonometry/Trigonometry.agda Algebra/Field.agdai
	agda $<

ClassicalTopology/Topology.agdai: ClassicalTopology/Topology.agda Set.agdai
	agda $<

Data/Bool.agdai: Data/Bool.agda Algebra/Field.agdai Relations.agdai
	agda $<

Data/Integer.agdai: Data/Integer.agda Data/Natural.agdai Algebra/CRing.agdai
	agda $<

Algebra/Matrix.agdai: Algebra/Matrix.agda Algebra/Linear.agdai Data/Finite.agdai
	agda $<

Data/Finite.agdai: Data/Finite.agda Data/Natural.agdai
	agda $<

Data/Natural.agdai: Data/Natural.agda Algebra/Monoid.agdai Algebra/MultAdd.agdai Relations.agdai
	agda $<

Algebra/Linear.agdai: Algebra/Linear.agda Algebra/Field.agdai Algebra/Module.agdai
	agda $<

Algebra/Module.agdai: Algebra/Module.agda Algebra/CRing.agdai Set.agdai
	agda $<

Algebra/Metric.agdai: Algebra/Metric.agda Algebra/OrderedRng.agdai
	agda $<

Algebra/OrderedRng.agdai: Algebra/OrderedRng.agda Algebra/Field.agdai Relations.agdai
	agda $<

Algebra/Field.agdai: Algebra/Field.agda Algebra/CRing.agdai
	agda $<

Algebra/CRing.agdai: Algebra/CRing.agda Algebra/Ring.agdai
	agda $<

Algebra/Ring.agdai: Algebra/Ring.agda Algebra/Rng.agdai
	agda $<

Algebra/Rng.agdai: Algebra/Rng.agda Algebra/Group.agdai Algebra/MultAdd.agdai
	agda $<

Algebra/MultAdd.agdai: Algebra/MultAdd.agda Prelude.agdai
	agda $<

Algebra/Group.agdai: Algebra/Group.agda Algebra/Monoid.agdai
	agda $<

Algebra/Monoid.agdai: Algebra/Monoid.agda Prelude.agdai
	agda $<

Set.agdai: Set.agda Relations.agdai
	agda $<

Relations.agdai: Relations.agda Prelude.agdai
	agda $<

Prelude.agdai: Prelude.agda
	agda $<

.PHONY: clean
clean:
	find -type f -name "*\.agdai" -exec rm {} \;
