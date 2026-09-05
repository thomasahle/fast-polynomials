import FastPoly.Admissible
import FastPoly.Automorphism
import FastPoly.Instantiation
import FastPoly.Recover.Context
import FastPoly.Recover.Filtered
import FastPoly.Recover.KnownBlock
import FastPoly.Recover.Combination
import FastPoly.Recover.Multiplication
import FastPoly.Recover.Power
import FastPoly.Recover.XAlpha
import FastPoly.Recover.BasePairs
import FastPoly.Recover.Triangular
import FastPoly.Polynomial.TopWindow
import FastPoly.Polynomial.PeelMonic
import FastPoly.Polynomial.MonicFromPower
import FastPoly.Polynomial.SquareGadget
import FastPoly.Polynomial.ScalarShift
import FastPoly.Polynomial.MonicDivision
import FastPoly.Section4.FillTwo
import FastPoly.Section4.Fill
import FastPoly.Section4.FillRec
import FastPoly.Section4.Peeled
import FastPoly.Section4.PeeledCert
import FastPoly.Cost.PeeledCircuit
import FastPoly.Section4.Unitriangular
import FastPoly.Section4.FillCert
import FastPoly.Examples.Q3
import FastPoly.Section5.T
import FastPoly.Section5.Binomial
import FastPoly.Section5.Slopes
import FastPoly.Section5.UBinomial
import FastPoly.Section5.Rk2lEven
import FastPoly.Section5.Rk2lOdd
import FastPoly.Section5.Rk2l
import FastPoly.Section5.RSlots
import FastPoly.Section5.CertEngines
import FastPoly.Section5.Rk2lTri
import FastPoly.Section5.Rk2lTriEven
import FastPoly.Section5.Rk2lTriOdd
import FastPoly.Section5.Rk2lTriOddBase
import FastPoly.Section5.Rk2lTriMaster
import FastPoly.Section5.PerturbedT
import FastPoly.Section5.FourKPlusOne
import FastPoly.Section5.QFourKOne
import FastPoly.Section5.SlotSurj
import FastPoly.Section6.SpecialCases
import FastPoly.Section6.QOddDegree
import FastPoly.Section6.GadgetDecoders
import FastPoly.Section6.Dispatch
import FastPoly.Main
import FastPoly.Section6.Induction
import FastPoly.Examples.Septic
import FastPoly.Examples.SepticAdditions
import FastPoly.Examples.BarredPivot
import FastPoly.Examples.BarQ15
import FastPoly.Examples.BarQ15Structural
import FastPoly.Examples.BarQGeneral
import FastPoly.Examples.BarredGadgets
import FastPoly.Examples.OptimizedCircuits
import FastPoly.Examples.Chain17Bridge
import FastPoly.Examples.Char2Inverse
import FastPoly.Polynomial.MonicEvaluation
import FastPoly.Examples.Char2SmallInverses
import FastPoly.Examples.Char2Finite
import FastPoly.Examples.ExplicitEvaluationInverse
import FastPoly.Examples.Char2UpdateTriangular
import FastPoly.Examples.Char2PivotUpdates
import FastPoly.Examples.Char2Degree17GateCoordinates
import FastPoly.Examples.Char2RecoveredProductUpdates
import FastPoly.Examples.Char2Degree17TriangularCoordinates
import FastPoly.Examples.Char2Degree19Shell
import FastPoly.Examples.Char2Degree19Crown
import FastPoly.Examples.Char2Degree19Coordinates
import FastPoly.Examples.Char2Degree19Targets
import FastPoly.Examples.Char2Degree19InnerSimple
import FastPoly.Examples.Char2Degree19InnerZChanges
import FastPoly.Examples.Char2Degree19Realization
import FastPoly.Examples.Char2Degree19Bijection
import FastPoly.Examples.Char2Degree21Realization
import FastPoly.Examples.Char2Degree23Terminal
import FastPoly.Examples.Char2Degree23RowEight
import FastPoly.Examples.Char2Degree23Coordinates
import FastPoly.Examples.Char2Degree23Keys
import FastPoly.Examples.Char2Degree23Frame
import FastPoly.Examples.Char2Degree23Cancellations
import FastPoly.Examples.Char2Degree23HighFrame
import FastPoly.Examples.P15
import FastPoly.Examples.P27
import FastPoly.Examples.P27Composition
import FastPoly.Examples.P27Full
import FastPoly.Examples.P31
import FastPoly.Examples.P31Full
import FastPoly.Cost.Final
import FastPoly.Cost.Additions
import FastPoly.Cost.Additions.Realization
import FastPoly.Height.Depth
import FastPoly.Height.PeeledCircuit
import FastPoly.Height.ConstructionDepth
import FastPoly.Height.TCircuitDepth
import FastPoly.Height.RealizationDepth
import FastPoly.HeightFinal
import FastPoly.PaperMain
import FastPoly.LowerBound.General.Main
import FastPoly.LowerBoundChar2.General
import FastPoly.LowerBoundChar2.Sharpness

/-!
# FastPoly

Formalization of the decodable polynomial constructions of
*Fast Evaluation of Polynomials with Rational Preprocessing*.

Architecture (see `FastPoly/Recover/Context.lean` for the semantic layer):

* `Recover/Context`: relative visible algebras `𝒱(K, Φ, G, t)` and compatible pairs.
* `Recover/Filtered`: scalar and block triangular recovery (the proof engine for pivot tables).
* `Polynomial/TopWindow`: top-coefficient calculus for products with monic polynomials.
-/
