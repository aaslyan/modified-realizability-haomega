import HAomega.ExtractedEngines

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

end HAomega
