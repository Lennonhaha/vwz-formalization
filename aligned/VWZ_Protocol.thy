(*  Title:      VWZ_Protocol.thy
    SPDX-License-Identifier: Apache-2.0

    VWZ A3 -- stage 1 of the "definition layer" campaign.

    Normative source: fibemate-vwz-specification_20260906.md (v0.2.0-spec),
    sections 3.4, 3.5, 3.6, 4, 5, 6.2, 8.  This file contains DEFINITIONS ONLY
    -- no lemma and no property is proved here.

    Scope of stage 1 (the five named objects plus the minimum supporting
    machinery):
      * data model: pkey / skey / sigrec (spec Sec 3.6, Sec 6);
      * x1_of      -- the secret vector x1 (spec Sec 3.4);
      * t_of       -- the sparse target (spec Sec 5; the SHAKE-256 XOF itself is
                      not modelled, so hash_target stays an uninterpreted
                      constant, but the Sec 5.1 rejection bound is concrete);
      * adapted_of -- the adapted target (spec Sec 6.2);
      * deser_pk / deser_sig -- the Sec 8 parsers (inverses of ser_pk / ser_sig
                      up to the Sec 8.3 length checks).
    The evaluation equation of Sec 4 (eval) is included because t_of and the
    signature side both refer to it.

    Objects whose bodies need machinery not yet formalised (SHAKE-256 XOF,
    Gauss-Jordan, the keygen/signing RNG) remain `consts` tagged TODO(define).
    Anchoring the T1-D / T2 obligations onto this layer is a later stage.
*)
theory VWZ_Protocol
  imports VWZ_Fq3329 VWZ_Matrix
begin

section \<open>Know how the spec names its tuples\<close>

text \<open>Field elements are integers in @{text "[0, q)"} (spec Sec 2); matrices
  are of type @{typ mat} (@{typ "int list list"}).  The public key is
  @{text "(k, psi)"} with @{text "psi :: n x m x m"} (spec Sec 3.6); the
  signature is @{text "(w2, w3)"} (spec Sec 6); the secret key is the 10-tuple
  of spec Sec 3.6.\<close>

record pkey =
  pk_k   :: nat
  pk_psi :: "int list list list"   \<comment> \<open>n x m x m, each entry in [0, q)\<close>

record sigrec =
  sg_k  :: nat
  sg_w2 :: "int list"
  sg_w3 :: "int list"

record skey =
  sk_k     :: nat
  sk_lam_a :: "int list"
  sk_lam_b :: "int list"
  sk_lam_c :: "int list"
  sk_a2inv :: mat
  sk_a3inv :: mat
  sk_m2    :: mat
  sk_m3    :: mat
  sk_x1    :: "int list"
  sk_seed  :: nat

section \<open>Spec 3.5 -- Vandermonde row\<close>

definition vand :: "int \<Rightarrow> nat \<Rightarrow> int list" where
  "vand lam m = map (\<lambda>j. (lam ^ j) mod 3329) [0..<m]"

section \<open>Spec 4 -- public evaluation\<close>

definition matvec :: "mat \<Rightarrow> int list \<Rightarrow> int list" where
  "matvec A v = map (\<lambda>row. dot row v) A"

definition eval_slice :: "mat \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int" where
  "eval_slice S w2 w3 = dot w2 (matvec S w3) mod 3329"

definition eval :: "pkey \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> int list" where
  "eval pk w2 w3 = map (\<lambda>S. eval_slice S w2 w3) (pk_psi pk)"

section \<open>Spec 3.4 -- the secret vector x1\<close>

definition x1_of :: "skey \<Rightarrow> int list" where
  "x1_of sk = sk_x1 sk"

section \<open>Spec 5 -- message to sparse target\<close>

text \<open>HashToTarget is SHAKE-256 (XOF reader) followed by the partial
  Fisher-Yates selection and the Sec 5.1 rejection sampler; only the arithmetic
  core of the sampler is formalised.  The XOF constant hash_target is the
  nat-valued one from VWZ_Fq3329 (one source of truth); t_of coerces its
  result into the int-valued field-element world used here.\<close>

definition reject_bound :: "nat \<Rightarrow> nat" where
  "reject_bound N = (65536 div N) * N"

definition t_of :: "pkey \<Rightarrow> nat list \<Rightarrow> int list" where
  "t_of pk msg = map int (hash_target (pk_k pk) msg)"

section \<open>Spec 6.2 -- adapted target\<close>

definition adapted_of :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "adapted_of t x1 = map2 (\<lambda>a b. a * invmod b mod 3329) t x1"

section \<open>Spec 8 -- deserialization\<close>

text \<open>Every field element is unsigned 16-bit little-endian (spec Sec 8), so the
  pair @{text "(lo, hi)"} decodes to @{text "lo + 256 * hi"}.  Sec 8.3 requires
  the length check to be keyed on the single byte @{text "k"}.\<close>

definition decode2 :: "nat list \<Rightarrow> nat list option" where
  "decode2 xs =
     (if even (length xs)
      then Some (map (\<lambda>i. xs ! (2 * i) + 256 * xs ! (2 * i + 1))
                     [0..<length xs div 2])
      else None)"

definition deser_pk :: "nat list \<Rightarrow> nat list option" where
  "deser_pk bs =
     (case bs of
        [] \<Rightarrow> None
      | (k # rest) \<Rightarrow>
          (if length rest = 2 * par_n k * par_m k * par_m k
           then decode2 rest else None))"

definition deser_sig :: "nat list \<Rightarrow> nat list option" where
  "deser_sig bs =
     (case bs of
        [] \<Rightarrow> None
      | (k # rest) \<Rightarrow>
          (if length rest = 4 * par_m k then decode2 rest else None))"

end
