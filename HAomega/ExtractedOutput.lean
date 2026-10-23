import HAomega.ExtractedEngines
import HAomega.ClosedFourierODE

namespace HAomega

#eval IO.println ("\n=== 1. CAUCHY-KOWALEVSKI ANALYTIC PDE ENGINE ===")
#eval IO.println ("RAW LAMBDA TERM:\n" ++ ckRawLambda)
#eval IO.println ("\nCOLLAPSED FUNCTIONAL PROGRAM:\n" ++ ckCollapsedLambda)
#eval IO.println ("\nEMITTED HASKELL SOURCE:\n" ++ ckHaskellSource)

#eval IO.println ("\n=== 2. NEWTON-RAPHSON INVERTER ===")
#eval IO.println ("RAW LAMBDA TERM:\n" ++ newtonRawLambda)
#eval IO.println ("\nCOLLAPSED FUNCTIONAL PROGRAM:\n" ++ newtonCollapsedLambda)
#eval IO.println ("\nEMITTED HASKELL SOURCE:\n" ++ newtonHaskellSource)

#eval IO.println ("\n=== 3. SYMPLECTIC KEPLER INTEGRATOR ===")
#eval IO.println ("RAW LAMBDA TERM:\n" ++ symplecticRawLambda)
#eval IO.println ("\nCOLLAPSED FUNCTIONAL PROGRAM:\n" ++ symplecticCollapsedLambda)
#eval IO.println ("\nEMITTED HASKELL SOURCE:\n" ++ symplecticHaskellSource)

#eval IO.println ("\n=== 4. EXTRACTED SYSTEM T JET CALCULUS & E1 MODULI ENGINE ===")
#eval IO.println ("FTC ANTIDERIVATIVE HASKELL:\n" ++ jetIntegHaskellSource)
#eval IO.println ("\nCAUCHY CONVOLUTION HASKELL:\n" ++ jetMulHaskellSource)
#eval IO.println ("\nPOLYNOMIAL EVALUATOR HASKELL:\n" ++ jetEvalPolyHaskellSource)
#eval IO.println ("\nEXTRACTED E1 CAUCHY MODULUS (GENUINE PROOF-COMPUTED) HASKELL:\n" ++ jetCauchyModGenuineHaskellSource)
#eval IO.println ("\nEXTRACTED E1 CAUCHY MODULUS (WITNESS-STYLE) HASKELL:\n" ++ jetCauchyModHaskellSource)
#eval IO.println ("\nEXTRACTED E1 CONTINUITY MODULUS HASKELL:\n" ++ jetContModHaskellSource)
#eval IO.println ("\nEXTRACTED E1 DIFFERENTIABILITY MODULUS HASKELL:\n" ++ jetDiffModHaskellSource)
#eval IO.println ("\nNEWTON-SCHULZ JET INVERTER HASKELL:\n" ++ newtonJetInvHaskellSource)
#eval IO.println ("\nRICCATI NONLINEAR ODE PICARD SOLVER HASKELL:\n" ++ riccatiPicardHaskellSource)

end HAomega
