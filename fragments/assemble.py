from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent
names=['FiniteCarrier.lean','GaussComponents.lean','RelativeResolvent.lean',
 'RelativeAnalytic.lean','Mollifier.lean','CompactApproximation.lean',
 'WeightedRegularity.lean',
 'RelativeLaplace.lean','SmoothCandidate.lean',
 'ArchimedeanCutoff.lean','FactorialSpine.lean','SpectralTail.lean',
 'PositivityBalance.lean','PoleCompensation.lean','FourierDecay.lean',
 'AngularDecay.lean','AnalyticObligations.lean',
 'ScaledCutoff.lean','EndpointIBP.lean','WeightedBulk.lean',
 'WeightedConvolution.lean','WeightedBulkComplex.lean','ProbabilityKernel.lean',
 'ConvolutionTransfer.lean','MollifierBulkBounds.lean','CompactParameters.lean',
 'ActualDerivatives.lean','CutoffProductBounds.lean','CompactDerivativeBounds.lean',
 'CandidateFourierBounds.lean','WeightedFourierBounds.lean',
 'ParameterHolomorphy.lean','ConcreteApproximation.lean','MultiplicityMajorant.lean','CountScale.lean','TransformLimit.lean','SpectralSum.lean','AnalyticZeroSum.lean','ZetaSpectralSum.lean','LogDerivativeObstruction.lean','GeometricPoleLimit.lean','ArchimedeanLimit.lean','RealPlaceLimit.lean','EulerGeometricLimit.lean','CompensatedZetaLimit.lean','FinitePrimeSupport.lean','SpectralHolomorphic.lean','RealPlaceHolomorphic.lean','ZetaContinuationCriterion.lean','RestrictedTraceLimit.lean','RestrictedTraceZeroFree.lean','CofinalTraceCriterion.lean','ActualRestrictedZetaTrace.lean','RestrictedTraceEquivalence.lean','AsymptoticTraceCriterion.lean','DirichletGeometricLimit.lean','ZetaPoleRemoved.lean','ParityRealPlace.lean','JensenZeroCount.lean','MellinGrowth.lean','ZetaMellinSplit.lean','CompletedZetaGrowth.lean','EntireXiOrders.lean','ActualZetaZeroCount.lean','RealPlaceBranches.lean','ZetaTraceCountDischarged.lean','AnalyticZeroResidue.lean','ZetaRadialSummability.lean','CanonicalFactor.lean','ZetaCanonicalProduct.lean','ZetaProductZeros.lean','ZetaProductLogDerivative.lean','HadamardRelative.lean','XiEulerMatch.lean','EntireXiZeroSet.lean','RealPlaceSeries.lean','GammaSeqUniform.lean','GammaSeqLogDerivative.lean','RelativeGammaFactor.lean','ZetaProductOrders.lean','ZetaThreeHalvesSum.lean','EntireQuotient.lean','CanonicalProductGrowth.lean','CompensatedEulerSpectral.lean','EntireXiGrowth.lean','AffineFromRealPart.lean','HadamardGrowthConsequence.lean','QuotientMeanGrowth.lean','ZetaHadamardComplete.lean','RelativeVerticalMajorant.lean','LineResidualEquivalence.lean','FourierTestInversion.lean','ResolventFourierPairing.lean','RealPlaceFourierPairing.lean','SpectralFourierPairing.lean','PrimeFourierPairing.lean','ZetaFullFiniteFormula.lean','FixedStripTraceEquivalence.lean','DirichletGammaRelative.lean','DirichletZeroSet.lean','WeakFEPairMellinSplit.lean','HurwitzTailGrowth.lean','EntireGrowthEnvelope.lean','GenericThreeHalvesSum.lean','NormalizedEntireQuotient.lean','EntireCanonicalProduct.lean','HurwitzMellinEnvelope.lean','EntireProductLogDerivative.lean','DirichletZeroCount.lean','EntireHadamard.lean','DirichletFourierPairing.lean','DirichletHadamard.lean','DirichletEulerSpectral.lean','GenericSpectralFourierPairing.lean','ParityRealPlaceFourierPairing.lean','DirichletFullFiniteFormula.lean','DirichletPrimitiveReduction.lean','DirichletRestrictedResidual.lean','DirichletConjugation.lean','DirichletResidualForward.lean','DirichletFullCriterion.lean','RelativeSpectrumAnalytic.lean','SpectralCarrierDomain.lean','RelativeSpectrumRigidity.lean','ArithmeticFourierInversion.lean','ArithmeticFourierGrowth.lean','CoherentEnergyBounds.lean','MertensToZetaResidual.lean','DirichletImprimitiveFiniteFormula.lean','CoherentEnergyTraceBridge.lean','ZetaSpectralWeightIdentification.lean','ZetaAbelGrowth.lean','ZetaEulerNearOne.lean','DiskNormInterpolation.lean','ZetaDiskLog.lean','ZetaOnMovingDisks.lean','ZetaReciprocalSlowGrowth.lean','ZetaReciprocalUniform.lean','VerticalIntegralShift.lean','PerronRampBounds.lean','PerronRampIntegral.lean','PerronRamp.lean','MertensRampApproximation.lean','SmoothedPerronEuler.lean','SmoothedPerronShift.lean','MertensConverse.lean','SmoothedLSeriesEuler.lean','ChebyshevRampApproximation.lean','ChebyshevToResidual.lean','StripEvaluationWitness.lean','StripDerivativeWitness.lean','PerronGrowthTransfer.lean','ChebyshevDesmoothing.lean','ChebyshevLogDerivativeGrowth.lean','SmoothedPoleEuler.lean','SmoothedPoleApproximation.lean','ChebyshevConverse.lean','PrimeAtomValue.lean','PrimeAtomBumps.lean','CompensatedGeometryUnbounded.lean','FiniteSpectralTailObstruction.lean','ZetaThreePointPositivity.lean','ZetaCanonicalPositive.lean','RealPlaceLogGrowth.lean','ZetaLogarithmicExclusion.lean','ZetaLogarithmicRegion.lean','CompactSpectralSummability.lean','ScaledCompactTest.lean','SmoothedPrimeExplicitLimit.lean','SmoothedPrimeError.lean','UnrestrictedCompactPrimeLimit.lean','CompactPrimeSandwichTests.lean','SharpPrimeNumberTheorem.lean','ArithmeticFourierShell.lean','ArithmeticFourierPairBlock.lean','ArithmeticFourierShellMertens.lean','ArithmeticFourierComplementBound.lean','PrimeHalfShellCount.lean','ArithmeticFourierPrimePartners.lean','ArithmeticFourierPrimeMatching.lean','OptimalFourierPairing.lean','ArithmeticFourierShellGrowth.lean',
 'ArithmeticFourierIncrement.lean','ArithmeticFourierTouchedCost.lean',
 'ArithmeticFourierShortEstimate.lean','ArithmeticFourierFullCorrelation.lean',
 'ArithmeticFourierShortMass.lean','ArithmeticFourierShortSelection.lean','ArithmeticFourierShortPower.lean',
 'PositiveLaplaceMoments.lean','ArithmeticFourierDyadicConvolution.lean',
 'ArithmeticFourierDenseTests.lean','ArithmeticFourierDyadicAbel.lean','ArithmeticFourierDyadicKernel.lean',
 'ArithmeticFourierParityInverse.lean','RadixFloor.lean','MixedRadix.lean','RankPairingCore.lean','RadixActualRankPairing.lean','ArithmeticFourierRankCost.lean','ArithmeticFourierRankRestricted.lean','PositiveComplexLaplace.lean','NontrivialZeroExistence.lean','PrimeErrorLaplace.lean','ArithmeticFourierWeakOscillation.lean']
names += ['PrimeErrorSignChanges.lean', 'SquarefreeIntervalActivity.lean', 'ArithmeticFourierRankGram.lean', 'ArithmeticFourierRankBandwidth.lean', 'ArithmeticFourierDyadicBandwidth.lean', 'RadixMellin.lean', 'RadixSampling.lean', 'SmoothedPrimeUniform.lean', 'SmoothedPrimeSandwichUniform.lean', 'SharpChebyshevError.lean', 'UnconditionalDyadicLogSaving.lean', 'BlockIntervalShift.lean', 'BlockCutoffIntervals.lean', 'BlockDirichletBound.lean', 'BlockDirichletMoments.lean', 'BlockJacksonSpectrum.lean', 'BlockIntervalEnergy.lean', 'BlockJacksonMoment.lean', 'ActualBlockEnergySmoothing.lean', 'BlockWeightedVariance.lean', 'BlockIntervalVariance.lean']
names += ['BlockEndpointBounds.lean', 'ActualBlockEndpointEnergy.lean']
names += ['ReciprocalLocalComparison.lean', 'ReciprocalEulerDisk.lean', 'ReciprocalMovingDisk.lean', 'ReciprocalHighLogStrip.lean', 'ReciprocalUniformLogStrip.lean', 'FinitePerronRectangle.lean', 'FinitePerronTails.lean', 'FinitePerronMertens.lean', 'QuantitativeMertens.lean', 'UnconditionalMertens.lean', 'UnconditionalRankRestricted.lean', 'ArithmeticFourierDyadicOrthogonal.lean', 'MobiusCrossingLengths.lean', 'BlockFlatTop.lean', 'WeightedVariancePairs.lean', 'DyadicEndpointPower.lean', 'ChebyshevDyadicPower.lean', 'AstraPrimeRightCut.lean', 'AstraPrimeRightFinite.lean', 'AstraPrimeRightEndpoint.lean', 'PhaseWindow.lean', 'PhaseWindowFactors.lean', 'UniformPhaseIsolation.lean']
names += ['MobiusRankLocalization.lean', 'RankNormalizedGeometry.lean', 'LocalizedCrossingGroups.lean', 'RankScaleWindow.lean', 'RealDyadicMesh.lean', 'UniformGridRounding.lean', 'RankCenteredContrast.lean', 'RankGroupMean.lean', 'RankContrastTransfer.lean', 'RankFittedConstant.lean', 'CenteredDistanceTransfer.lean', 'AstraLocalModeContrast.lean', 'AstraUnitRotatedContrast.lean', 'ZeroPrimitiveMean.lean', 'ZeroPrimitiveBounds.lean', 'ContinuumModeExpansion.lean', 'PhaseDensityTransfer.lean', 'ExponentialCountTransfer.lean', 'WeightedRightDensity.lean', 'ZetaRightDensity.lean', 'ActualWeightedRightDensity.lean', 'FiniteZeroPotential.lean', 'ThreeConditionTrim.lean', 'StripObstructionExponent.lean', 'MertensFixedPower.lean', 'FrozenWindowObstruction.lean', 'FrozenRankWindowTransfer.lean', 'BlockComplexTransfer.lean', 'ComplexCyclicPotential.lean', 'FrozenShellGridError.lean', 'AstraSharpRadialTail.lean', 'AstraRampVariation.lean', 'AstraSharpZeroRemainder.lean', 'AstraSharpRightEndpoint.lean', 'AstraSharpDyadicX.lean', 'AstraSharpIndividual.lean', 'ActualRightInverseHeight.lean', 'ActualLongRankModel.lean']
names += ['BoundedComplexCenter.lean', 'LongRankStripForward.lean', 'FreezeActualSpectralRows.lean', 'ActualNormalizedRankWindow.lean', 'ActualLongRankCenter.lean', 'ObservableLongRows.lean', 'WindowCostAlgebra.lean', 'LongRankGridConnection.lean', 'ActualTargetZeroSet.lean', 'ActualWindowLongRankBound.lean', 'RankStripAsymptotics.lean', 'WindowUniformObserver.lean', 'LongRankStripEquivalence.lean']
names += ['IntegerPhaseSampling.lean', 'FrozenPotentialShift.lean', 'ActualSampledRankWindow.lean', 'IntegerWindowObserver.lean', 'NaturalLongRankStripEquivalence.lean', 'FixedStripReciprocal.lean', 'FixedStripFourierGrowth.lean', 'RankStripFourierConnection.lean', 'FixedStripLogDerivative.lean', 'ChebyshevFixedPowerConverse.lean', 'FixedStripChebyshev.lean', 'SharpRetainedStripBound.lean', 'RetainedAmplitudeCriterion.lean', 'ParametricSharpZeroRemainder.lean', 'ParametricSharpDyadic.lean', 'ParametricAmplitudeCriterion.lean']
names += ['PositiveSummatoryPower.lean', 'OneSidedPrimePower.lean', 'OneSidedDyadicPower.lean', 'FourierEulerFactor.lean', 'OneSidedFourierScalar.lean', 'OneSidedRHCriteria.lean', 'OneSidedNaturalDyadic.lean']
names += ['ZetaConjugateMultiplicity.lean', 'RealRetainedSpectral.lean', 'RealRankCenter.lean', 'ParametricSignedSharp.lean', 'SignedRetainedCriterion.lean']
names += ['RieszPrimeMellin.lean','RieszFiniteRamp.lean','RieszSignedCriterion.lean']
names += ['SignedModeExcursions.lean','RieszNaturalRounding.lean']
imports=set();bodies=[];pins={};decls=[]
for name in names:
    p=root/name
    pins[name]=hashlib.sha256(p.read_bytes()).hexdigest()
    lines=[]
    stack=[]
    for line in p.read_text(encoding='utf-8').splitlines():
        code=line.strip()
        if code.startswith('namespace '):
            stack.append(('namespace',code.split()[1]))
        elif code=='noncomputable section' or code=='section' or code.startswith('section '):
            stack.append(('section',None))
        elif code=='end' or code.startswith('end '):
            assert stack,(name,code)
            stack.pop()
        m=re.match(r'theorem (\w+)(?:\s*[:({]|$)',line)
        if m:
            ns=[value for kind,value in stack if kind=='namespace']
            decls.append('.'.join(ns+[m[1]]))
        if line.startswith('import '):
            if line.startswith('import Mathlib.'):
                imports.add(line)
        else:
            lines.append(line)
    body='\n'.join(lines)
    assert all(kind=='section' for kind,_ in stack),(name,stack)
    body+='\nend\n'*len(stack)
    bodies.append('/- BEGIN '+name+' -/\n'+body+'\n/- END '+name+' -/')
out='/- Generated by assemble.py. Fragment hashes: ASSEMBLY.json. -/\n'
out+='\n'.join(sorted(imports))+'\n\n'+'\n\n'.join(bodies)+'\n'
out+='\n/- Complete exported-theorem axiom audit. -/\n'
out+='\n'.join('#print axioms '+name for name in decls)+'\n'
definitions=['RHConnections.AnalyticObligations.concreteApproximation'] if 'ConcreteApproximation.lean' in names else []
out+='\n'.join('#print axioms '+name for name in definitions)+'\n'
(root/'Verified.lean').write_text(out,encoding='utf-8')
(root/'ASSEMBLY.json').write_text(json.dumps({'fragments':pins,'theorems':decls,
 'certified_definitions':definitions,
 'aggregate_sha256':hashlib.sha256((root/'Verified.lean').read_bytes()).hexdigest()},indent=2)+'\n',encoding='utf-8')
print(f'Assembled {len(names)} fragments, {len(decls)} theorems, into Verified.lean.')



































