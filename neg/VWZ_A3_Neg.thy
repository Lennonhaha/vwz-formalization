(* SPDX-License-Identifier: Apache-2.0
   VWZ A3 smoke -- NEGATIVE CONTROL

   This file MUST FAIL to build. If `isabelle build` reports success here, the
   smoke test is a rubber stamp and no result from VWZ_A3_Smoke may be trusted.

   The claim below is false for every k >= 1 (the true value is k+1), so the
   proof method must fail and the build must exit non-zero.
*)

theory VWZ_A3_Neg
  imports Main
begin

lemma neg_control_is_false:
  "1 <= (k::nat) ==> 2 * k + 2 - (k + 1) = 1"
  by arith

end
