theory VWZ_Probe
  imports VWZ_KeyGen
begin

text \<open>Two tiny checks, both cheap to evaluate (no LCG, no det).\<close>

lemma probe_mult: "mat_mult (row_add_matrix 2 0 1 1) [[1,3328],[0,1]] = [[1,3329],[0,1]]"
  by eval

lemma probe_rowop: "add_row_mult [[1,3328],[0,1]] 0 1 1 = [[1,0],[0,1]]"
  by eval

lemma probe_mismatch:
  "mat_mult (row_add_matrix 2 0 1 1) [[1,3328],[0,1]]
   \<noteq> add_row_mult [[1,3328],[0,1]] 0 1 1"
  by eval

end
