(*
  CST_Model.thy  --  EXTp / Counterfactual Soundness Theorem
  =========================================================
  PHASE 0: Pure EXTp model (executable defs) + PHASE 1 locale skeleton.

  This file is the base layer for lifting the semi-formal proof of App A to
  a machine-checked CONDITIONAL theorem. It DELIBERATELY does not touch the
  seL4 harness OR the lifting gap -- because the conditional theorem (with
  A1-A4 taken as hypotheses) is independent of the lifting. The lifting only
  enters in Phase 3, if we want to discharge A1 for K_verified.

  Source correspondence:
    - datatypes/records    : extp.tex sec:framework, sec:soe, App A "Notation"
    - D (divergence)       : extp_formal_properties.md P2/P3, App A
    - envelope E           : extp.tex sec:cst, CST doc sec:3.4
    - four-step check      : extp.tex sec:intervention (1)-(4)
    - locale A1-A4         : extp.tex Table tab:assumptions, CST doc sec:3.2 / sec:5.4

  Status notes (PHASE 0 + PHASE 1 + PHASE 2 complete, NO sorry):
    - ALL definitions in this layer are total and executable (verified by eval).
    - The conditional theorem cst_conditional (Theorem 1, => direction) is PROVED;
      the three bounding lemmas (App A), the HP witness construction (AC2(b)),
      Proposition 1 (sequential composition) and the locale consistency
      interpretation are PROVED.
    - Probability bounds (delta_A1, eps_SOE, alpha) enter as ABSTRACT real
      parameters; Clopper-Pearson is NOT PROVED in Isabelle (it is a measurement)
      -- only the union-bound arithmetic is proved.
    - The only remaining open item = PHASE 3 (lifting), a deliberate stub in §7.
    - 2026-09-01 (§8): the two "prose" corners of the statement-fidelity audit closed:
      composition in W/K_fwk form (hold, pert_bounded, locale cst_composition,
      cst_conditional_W) + Prop 1 trace-chained (chain_ok, chain_extend,
      chain_conditional). Total 115 facts, NO sorry.
*)

theory CST_Model
  imports Complex_Main "HOL-Library.Word"
begin

section \<open>1. Observable surface and trace (SOE 4-tuple + timing)\<close>

text \<open>
  4-tuple observable surface (extp.tex sec:soe): rip, exit_reason,
  exit_qual, rax. In Phase 0 we use nat; it can later be converted to a 64-bit word.
\<close>

text \<open>
  (e) ACTUAL register widths: VT-x/VMCS fields are machine words.
  rip / exit_qual / rax = 64-bit; exit_reason = 32-bit VMCS field. The observable
  surface is compared only by EQUALITY (soe_clause), so converting to word
  CARRIES NO OVERFLOW RISK. timing REMAINS nat (TSC arithmetic; wraparound is
  deliberately out of scope -- the fresh-boot discipline provides short traces +
  in-session reset).
\<close>

record observable =
  rip         :: "64 word"
  exit_reason :: "32 word"
  exit_qual   :: "64 word"
  rax         :: "64 word"

text \<open>A VM-exit event: observable 4-tuple + per-event timing \<open>\<Delta>\<^sub>i\<close> (cycles).\<close>

record event =
  obs    :: observable
  timing :: nat

type_synonym trace = "event list"

definition aligned :: "trace \<Rightarrow> trace \<Rightarrow> bool" where
  "aligned To Tc \<longleftrightarrow> length To = length Tc"


section \<open>2. Divergence detection function D\<close>

text \<open>
  The two clauses of D (App A, extp_formal_properties.md):
    - SOE clause  : 4-tuple difference (deterministic, FPR = 0 under A4)
    - timing clause: |Delta_cf - Delta_orig| > Dstar (probabilistic, FPR <= alpha)
\<close>

definition soe_clause :: "trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool" where
  "soe_clause To Tc i \<longleftrightarrow> obs (To ! i) \<noteq> obs (Tc ! i)"

definition timing_clause :: "nat \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool" where
  "timing_clause Dstar To Tc i \<longleftrightarrow>
     \<bar>int (timing (Tc ! i)) - int (timing (To ! i))\<bar> > int Dstar"

definition D :: "nat \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool" where
  "D Dstar To Tc i \<longleftrightarrow> soe_clause To Tc i \<or> timing_clause Dstar To Tc i"

text \<open>Is there a divergence at any event on the trace?\<close>

definition diverges :: "nat \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  "diverges Dstar To Tc \<longleftrightarrow> (\<exists>i < length Tc. D Dstar To Tc i)"


subsection \<open>2.1 Separation and INDEPENDENCE of the AC2(a) witnesses\<close>

text \<open>
  App A item (iv): "The structural-clause version (4-tuple delta) and timing-clause
  version each INDEPENDENTLY witness AC2(a)." We carry this statement into the model:
  the two clauses of D are two SEPARATE witness types; D = (at least one witness fires).

  Mathematically, "independently" MEANS: neither one entails the other.
  We PROVE this with concrete counterexamples (witness_indep_* below),
  so the independence claim does not remain in prose.
\<close>

datatype ac2a_witness = StructuralW | TimingW

definition witnesses :: "ac2a_witness \<Rightarrow> nat \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool" where
  "witnesses w Dstar To Tc i \<longleftrightarrow>
     (case w of StructuralW \<Rightarrow> soe_clause To Tc i
              | TimingW     \<Rightarrow> timing_clause Dstar To Tc i)"

lemma witnesses_struct [simp]:
  "witnesses StructuralW Dstar To Tc i = soe_clause To Tc i"
  by (simp add: witnesses_def)

lemma witnesses_timing [simp]:
  "witnesses TimingW Dstar To Tc i = timing_clause Dstar To Tc i"
  by (simp add: witnesses_def)

text \<open>D is exactly the existence of a witness (separation of the OR-clause structure).\<close>

lemma D_iff_witness:
  "D Dstar To Tc i \<longleftrightarrow> (\<exists>w. witnesses w Dstar To Tc i)"
proof
  assume "D Dstar To Tc i"
  then show "\<exists>w. witnesses w Dstar To Tc i"
  proof (unfold D_def, elim disjE)
    assume "soe_clause To Tc i"
    then have "witnesses StructuralW Dstar To Tc i" by simp
    then show ?thesis ..
  next
    assume "timing_clause Dstar To Tc i"
    then have "witnesses TimingW Dstar To Tc i" by simp
    then show ?thesis ..
  qed
next
  assume "\<exists>w. witnesses w Dstar To Tc i"
  then obtain w where "witnesses w Dstar To Tc i" ..
  then show "D Dstar To Tc i" by (cases w) (simp_all add: D_def)
qed

text \<open>Each witness is sufficient ON ITS OWN (each independently witnesses).\<close>

lemma structural_witness_suffices:
  "soe_clause To Tc i \<Longrightarrow> D Dstar To Tc i"
  by (simp add: D_def)

lemma timing_witness_suffices:
  "timing_clause Dstar To Tc i \<Longrightarrow> D Dstar To Tc i"
  by (simp add: D_def)

text \<open>
  A sweep yields one RESULT per input: either an admissible claim (with a witness,
  Some w) or D=false (silent, None). `emitted_of` extracts the witness list of
  admissible claims only -- silent inputs are DROPPED.
\<close>

definition emitted_of :: "ac2a_witness option list \<Rightarrow> ac2a_witness list" where
  "emitted_of xs = map the (filter (\<lambda>x. x \<noteq> None) xs)"

lemma emitted_of_Nil [simp]: "emitted_of [] = []"
  by (simp add: emitted_of_def)

lemma emitted_of_None [simp]: "emitted_of (None # xs) = emitted_of xs"
  by (simp add: emitted_of_def)

lemma emitted_of_Some [simp]: "emitted_of (Some w # xs) = w # emitted_of xs"
  by (simp add: emitted_of_def)


subsection \<open>2.2 aligned: index safety and the operational statement of A4\<close>

lemma aligned_index_safe:
  "aligned To Tc \<Longrightarrow> i < length Tc \<Longrightarrow> i < length To"
  by (simp add: aligned_def)

text \<open>
  The operational statement of A4 (extp.tex sec:soe): with no intervention, aligned
  traces are pointwise equal on the 4-tuple. `aligned` does real work here:
  the i-th event EXISTS in both traces.
\<close>

lemma no_divergence_obs_eq:
  assumes "aligned To Tc" and "\<not> diverges Dstar To Tc"
  shows "\<forall>i < length Tc. obs (To ! i) = obs (Tc ! i) \<and> i < length To"
proof (intro allI impI conjI)
  fix i assume i: "i < length Tc"
  from assms(2) i have "\<not> D Dstar To Tc i" by (auto simp: diverges_def)
  then show "obs (To ! i) = obs (Tc ! i)"
    by (simp add: D_def soe_clause_def)
  from assms(1) i show "i < length To" by (rule aligned_index_safe)
qed


section \<open>3. Intervention model and validity envelope E\<close>

datatype scope = PerEvent | PerWindow | Global

datatype iclass = NopCount | RegWrite | InputValue | CachePreload

text \<open>
  do(X = x') at event i. In Phase 0, X and x' are nat ID/value; icls = intervention class.
  (CST doc sec:2.2 intervention surface.)
\<close>

record intervention =
  var      :: nat      \<comment> \<open>ID of the target variable X\<close>
  newval   :: nat      \<comment> \<open>x'\<close>
  at_event :: nat      \<comment> \<open>index of e_i\<close>
  icls     :: iclass

text \<open>
  Validity envelope E (extp.tex sec:cst, CST doc sec:3.4): a record with in-scope /
  out-of-scope sentinels. s_in = validated intervention surface
  (S_in), s_out = the silent channels outside (S_out).
\<close>

record envelope =
  instr    :: nat          \<comment> \<open>timing-instrument ID (S1 / S2)\<close>
  wl_class :: nat          \<comment> \<open>workload class\<close>
  gw_type  :: nat          \<comment> \<open>guest-workload type\<close>
  scp      :: scope
  s_in     :: "nat set"
  s_out    :: "nat set"

text \<open>
  CST v1.0 scope predicate (extp.tex sec:intervention step 1):
  only per-event scope and the four validated intervention classes.
\<close>

definition cst_v1_covered :: "envelope \<Rightarrow> intervention \<Rightarrow> bool" where
  "cst_v1_covered E \<iota> \<longleftrightarrow>
     scp E = PerEvent \<and>
     icls \<iota> \<in> {NopCount, RegWrite, InputValue, CachePreload} \<and>
     s_in E \<inter> s_out E = {}"          \<comment> \<open>S_in and S_out disjoint (wf condition)\<close>


subsection \<open>3.1 Semantics of the do-operator (Pearl severance)\<close>

text \<open>
  Pearl's do(X=x') "forces X to x' and severs all causal links into X"
  (extp.tex sec:background; App A item i "effectiveness"). We model the guest
  state as a variable-to-value valuation; apply_iv is the functional update that
  sets X to x'. Effectiveness = X reads x' after the intervention;
  severance = the result is INDEPENDENT of X's PREVIOUS value + the other
  variables are NOT TOUCHED (connected to modularity/composition).
\<close>

type_synonym valuation = "nat \<Rightarrow> nat"

definition apply_iv :: "intervention \<Rightarrow> valuation \<Rightarrow> valuation" where
  "apply_iv \<iota> \<sigma> = \<sigma>(var \<iota> := newval \<iota>)"

definition effective :: "intervention \<Rightarrow> bool" where
  "effective \<iota> \<longleftrightarrow> (\<forall>\<sigma>. apply_iv \<iota> \<sigma> (var \<iota>) = newval \<iota>)"

text \<open>Effectiveness: do() successfully sets X to x'.\<close>
lemma apply_iv_severs: "apply_iv \<iota> \<sigma> (var \<iota>) = newval \<iota>"
  by (simp add: apply_iv_def)

text \<open>Locality: variables other than X are unchanged (do() severs only the arrows into X).\<close>
lemma apply_iv_local: "y \<noteq> var \<iota> \<Longrightarrow> apply_iv \<iota> \<sigma> y = \<sigma> y"
  by (simp add: apply_iv_def)

text \<open>Severance: X's post-intervention value is independent of its PREVIOUS value.\<close>
lemma apply_iv_indep_pre: "apply_iv \<iota> \<sigma> (var \<iota>) = apply_iv \<iota> \<sigma>' (var \<iota>)"
  by (simp add: apply_iv_def)

text \<open>Effectiveness holds by construction for every intervention.\<close>
lemma effective_holds: "effective \<iota>"
  by (simp add: effective_def apply_iv_severs)

text \<open>Concrete example: reg_7 := 42; the target is forced, the neighbouring variable (3) is preserved.\<close>
lemma sanity_effective_forces:
  "apply_iv \<lparr> var = 7, newval = 42, at_event = 0, icls = RegWrite \<rparr> (\<lambda>_. 0) 7 = 42"
  by eval

lemma sanity_effective_local:
  "apply_iv \<lparr> var = 7, newval = 42, at_event = 0, icls = RegWrite \<rparr> (\<lambda>_. 5) 3 = 5"
  by eval


section \<open>4. Four-step admissibility check\<close>

text \<open>
  extp.tex sec:intervention: four steps before a claim is emitted.
    (1) the components of E match the CST v1.0 scope
    (2) the A1-A4 assumption references are present and current   (assum_ok flag)
    (3) D = true was actually observed at some event
    (4) X is on the validated intervention surface (var in S_in)
  Any one false -> no claim (structured invalidity tag).
\<close>

definition admissible ::
    "nat \<Rightarrow> envelope \<Rightarrow> intervention \<Rightarrow> bool \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  "admissible Dstar E \<iota> assum_ok To Tc \<longleftrightarrow>
     cst_v1_covered E \<iota>           \<comment> \<open>step 1\<close>
   \<and> assum_ok                        \<comment> \<open>step 2\<close>
   \<and> diverges Dstar To Tc           \<comment> \<open>step 3\<close>
   \<and> var \<iota> \<in> s_in E"                \<comment> \<open>step 4\<close>

text \<open>
  Claim emission = admissible (extp.tex: if the check passes EXTp emits a claim,
  otherwise an invalidity tag). Hence the (<=) direction of Theorem 1 -- "check
  passed => claim emitted" -- is true BY CONSTRUCTION (definitional).
\<close>

definition emits ::
    "nat \<Rightarrow> envelope \<Rightarrow> intervention \<Rightarrow> bool \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  "emits Dstar E \<iota> assum_ok To Tc \<longleftrightarrow> admissible Dstar E \<iota> assum_ok To Tc"

lemma left_direction:  \<comment> \<open>Theorem 1, (<=) direction -- PHASE 1, by construction\<close>
  "emits Dstar E \<iota> assum_ok To Tc \<longleftrightarrow> admissible Dstar E \<iota> assum_ok To Tc"
  by (simp add: emits_def)


section \<open>5. Sanity checks (executable)\<close>

definition ev :: "64 word \<Rightarrow> 32 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> event" where
  "ev r er eq a t =
     \<lparr> obs = \<lparr> rip = r, exit_reason = er, exit_qual = eq, rax = a \<rparr>, timing = t \<rparr>"

definition ex_orig :: trace where
  "ex_orig = [ ev 10 1 0 5 1000, ev 14 2 0 5 1050 ]"

text \<open>
  Sanity checks as PROVED facts (by eval) -- the machine verifies that the model
  computes correctly, not merely that it "typechecks".
\<close>

text \<open>Same trace, no intervention -> no divergence.\<close>
lemma sanity_no_divergence: "\<not> diverges 500 ex_orig ex_orig"
  by eval

text \<open>rax @1 changed (SOE clause) -> divergence.\<close>
lemma sanity_soe_clause:
  "diverges 500 ex_orig [ ev 10 1 0 5 1000, ev 14 2 0 9 1050 ]"
  by eval

text \<open>timing @0 jumped +2000 cycles, Dstar=500 (timing clause) -> True.\<close>
lemma sanity_timing_clause:
  "diverges 500 ex_orig [ ev 10 1 0 5 3000, ev 14 2 0 5 1050 ]"
  by eval

text \<open>timing @0 +400 cycles, Dstar=500 (below threshold) -> no divergence.\<close>
lemma sanity_below_threshold:
  "\<not> diverges 500 ex_orig [ ev 10 1 0 5 1400, ev 14 2 0 5 1050 ]"
  by eval


subsection \<open>5.1 Witness INDEPENDENCE -- proof by concrete counterexamples\<close>

text \<open>
  The mathematical content of the claim "Each INDEPENDENTLY witnesses AC2(a)":
  neither clause ENTAILS the other. Two counterexamples establish this definitively.
\<close>

definition ex_soe_only :: trace where    \<comment> \<open>rax @1 differs, timing SAME\<close>
  "ex_soe_only = [ ev 10 1 0 5 1000, ev 14 2 0 9 1050 ]"

definition ex_tim_only :: trace where    \<comment> \<open>timing @0 differs, 4-tuple SAME\<close>
  "ex_tim_only = [ ev 10 1 0 5 3000, ev 14 2 0 5 1050 ]"

text \<open>(1) The structural witness fires, the timing witness does NOT.\<close>
lemma witness_indep_structural:
  "witnesses StructuralW 500 ex_orig ex_soe_only 1
   \<and> \<not> witnesses TimingW 500 ex_orig ex_soe_only 1"
  by eval

text \<open>(2) The timing witness fires, the structural witness does NOT.\<close>
lemma witness_indep_timing:
  "witnesses TimingW 500 ex_orig ex_tim_only 0
   \<and> \<not> witnesses StructuralW 500 ex_orig ex_tim_only 0"
  by eval

text \<open>
  Result: the two witnesses are logically INDEPENDENT -- neither entails the other,
  nor can they be reduced to a common clause. Hence the OR structure of D
  really is two SEPARATE pieces of evidence, not two spellings of one.
\<close>

subsection \<open>5.2 A2 is NOT A TAUTOLOGY -- concrete evidence of falsifiability\<close>

text \<open>
  Reviewer objection: "Does A2 not merely restate the definition of D? I.e. is
  it a tautology?"
  ANSWER: No. A2 is a genuine, FALSIFIABLE claim -- because there ARE cases in
  which a REAL state difference is NOT reflected in D at all. A concrete one below:
  timing @0 differs by 400 cycles (a real perturbation), but D does not fire
  because it is BELOW the Dstar=500 threshold.

  If such a difference were a causal effect INSIDE S_in, A2 would be VIOLATED.
  So A2 is not an empty statement: it says something about the world and can
  turn out to be false. (This is the machine-checked counterpart of App A's
  "silent leak" / sub-Dstar class discussion.)
\<close>

definition ex_silent :: trace where   \<comment> \<open>timing @0 +400: a REAL difference, not reflected in D\<close>
  "ex_silent = [ ev 10 1 0 5 1400, ev 14 2 0 5 1050 ]"

lemma silent_effect_exists:
  "timing (ex_silent ! 0) \<noteq> timing (ex_orig ! 0)
   \<and> \<not> diverges 500 ex_orig ex_silent"
  by eval

text \<open>
  Moreover: this difference is invisible on the 4-tuple surface as well -- i.e. both clauses are silent.
\<close>

lemma silent_effect_invisible_on_both_clauses:
  "\<not> soe_clause ex_orig ex_silent 0 \<and> \<not> timing_clause 500 ex_orig ex_silent 0"
  by eval

lemma witnesses_logically_independent:
  "(\<exists>To Tc i Dstar. witnesses StructuralW Dstar To Tc i
                    \<and> \<not> witnesses TimingW Dstar To Tc i)
 \<and> (\<exists>To Tc i Dstar. witnesses TimingW Dstar To Tc i
                    \<and> \<not> witnesses StructuralW Dstar To Tc i)"
  using witness_indep_structural witness_indep_timing by blast


section \<open>6. CST assumption locale (A1-A4) -- PHASE 2: conditional theorem\<close>

text \<open>
  A1-A4 (extp.tex Table tab:assumptions) are ABSTRACT predicates; the probability
  bounds are ABSTRACT real parameters. p_soe / p_tim / p_conf = the MEASURED
  (unknown) contribution amounts in App A's three bounding arguments; the
  A1/A3/A4 assumptions BOUND them by eps_SOE / alpha / (delta_A1+alpha). Isabelle
  does not produce these reals -- they enter from outside, from the
  Clopper-Pearson / MI calibration; the theorem operates only on union-bound
  arithmetic + logical composition.

  eff_vars E = the observable-surface variables that "constitute the effect" in
  the event (in the HP witness construction, W = S_in \ eff_vars).
\<close>

locale cst_assumptions =
  fixes Dstar    :: nat
    and delta_A1 :: real        \<comment> \<open>CapSep empirical envelope (A1)\<close>
    and eps_SOE  :: real        \<comment> \<open>SOE Clopper-Pearson upper bound (A4)\<close>
    and alpha    :: real        \<comment> \<open>MI realized FPR (A3)\<close>
    and A1 :: "envelope \<Rightarrow> intervention \<Rightarrow> bool"   \<comment> \<open>modularity\<close>
    and A2 :: "envelope \<Rightarrow> intervention \<Rightarrow> bool"   \<comment> \<open>observational completeness / S_in\<close>
    and A3 :: "envelope \<Rightarrow> intervention \<Rightarrow> bool"   \<comment> \<open>confounder bound < Dstar\<close>
    and A4 :: "envelope \<Rightarrow> intervention \<Rightarrow> bool"   \<comment> \<open>replay determinism (SOE)\<close>
    and p_soe  :: "envelope \<Rightarrow> intervention \<Rightarrow> real"  \<comment> \<open>SOE-clause coincidence contribution\<close>
    and p_tim  :: "envelope \<Rightarrow> intervention \<Rightarrow> real"  \<comment> \<open>timing-clause coincidence contribution\<close>
    and p_conf :: "envelope \<Rightarrow> intervention \<Rightarrow> real"  \<comment> \<open>confounder contribution (modulo A1)\<close>
    and eff_vars :: "envelope \<Rightarrow> nat set"           \<comment> \<open>surface variables that produce the effect\<close>
    and effect_at :: "envelope \<Rightarrow> intervention \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool"
        \<comment> \<open>the UNDERLYING causal effect -- NOT D; specified independently\<close>
  assumes prob_nonneg: "0 \<le> delta_A1" "0 \<le> eps_SOE" "0 \<le> alpha"
      and prob_le_one:  "delta_A1 \<le> 1" "eps_SOE \<le> 1" "alpha \<le> 1"
      and A4_bounds_soe:  "\<And>E \<iota>. A4 E \<iota> \<Longrightarrow> 0 \<le> p_soe E \<iota> \<and> p_soe E \<iota> \<le> eps_SOE"
      and A3_bounds_tim:  "\<And>E \<iota>. A3 E \<iota> \<Longrightarrow> 0 \<le> p_tim E \<iota> \<and> p_tim E \<iota> \<le> alpha"
      and A1_bounds_conf: "\<And>E \<iota>. A1 E \<iota> \<Longrightarrow> 0 \<le> p_conf E \<iota> \<and> p_conf E \<iota> \<le> delta_A1 + alpha"
      and eff_subset:     "\<And>E. eff_vars E \<subseteq> s_in E"
      \<comment> \<open>A2's OPERATIONAL content: every causal effect INSIDE S_in is reflected in D.
          Note: the guard `var \<iota> \<in> s_in E` is essential -- A2 says NOTHING
          about S_out (App A: "explicitly out of A2's scope").\<close>
      and A2_manifests:
        "\<And>E \<iota> To Tc i. A2 E \<iota> \<Longrightarrow> var \<iota> \<in> s_in E
                        \<Longrightarrow> effect_at E \<iota> To Tc i \<Longrightarrow> D Dstar To Tc i"
begin

text \<open>
  The residual epistemic envelope App A reports per claim:
  residual = eps_SOE + delta_A1 + alpha (union bound). The bound of the AC2(b) W2 condition.
\<close>

definition residual :: real where
  "residual = eps_SOE + delta_A1 + alpha"

lemma residual_nonneg: "0 \<le> residual"
  using prob_nonneg by (simp add: residual_def)

lemma residual_le_three: "residual \<le> 3"
  using prob_le_one by (simp add: residual_def)


subsection \<open>6.1 Bounding lemmas (App A) -- proved\<close>

text \<open>
  The three "bounding" arguments of App A. Each one exports the upper bound that
  the corresponding assumption places on its contribution amount; the proof
  follows directly from the locale assumptions.
\<close>

\<comment> \<open>App A lem:coincidence-soe\<close>
lemma coincidence_soe_bound:
  assumes "A4 E \<iota>" shows "p_soe E \<iota> \<le> eps_SOE"
  using A4_bounds_soe[OF assms] by simp

\<comment> \<open>App A lem:coincidence-timing\<close>
lemma coincidence_timing_bound:
  assumes "A3 E \<iota>" shows "p_tim E \<iota> \<le> alpha"
  using A3_bounds_tim[OF assms] by simp

\<comment> \<open>App A lem:confounder (bounding modulo A1)\<close>
lemma confounder_bound:
  assumes "A1 E \<iota>" shows "p_conf E \<iota> \<le> delta_A1 + alpha"
  using A1_bounds_conf[OF assms] by simp


subsection \<open>6.15 Lemma silent -- scope-honest emission (App A lem:silent)\<close>

text \<open>
  App A's "Remark on lemma content" caveat: the content of the lemma is NOT
  "A2 implies its own scope" (that would be DEFINITIONAL); it is the CONSISTENCY
  of two INDEPENDENTLY specified components -- A2 (what is observable) and the
  emission policy (under which observation a claim is emitted).

  In the model this independence is STRUCTURAL:
    - `emits` / `admissible` are TOP-LEVEL definitions; they make NO reference to A2.
    - `A2` + `effect_at` are locale PARAMETERS; they make no reference to emission.
  The two lemmas below tie these two independent components together.
\<close>

text \<open>
  (i) SOUNDNESS direction: no claim is emitted WITHOUT observable divergence.
  Follows from the structure of the emission policy itself (A2 not needed).
\<close>

lemma emits_implies_divergence:
  "emits Dstar E \<iota> assum_ok To Tc \<Longrightarrow> diverges Dstar To Tc"
  by (simp add: emits_def admissible_def)

text \<open>
  (ii) SCOPE-COMPLETENESS direction: no causal effect INSIDE S_in goes
  UNREPORTED. Here A2 GENUINELY does work -- remove it and the lemma collapses.
\<close>

lemma silent_no_missed_effect:
  assumes "A2 E \<iota>" and "var \<iota> \<in> s_in E"
      and "effect_at E \<iota> To Tc i" and "i < length Tc"
  shows "diverges Dstar To Tc"
proof -
  from A2_manifests[OF assms(1) assms(2) assms(3)] have "D Dstar To Tc i" .
  with assms(4) show ?thesis by (auto simp: diverges_def)
qed

text \<open>
  (iii) Full form: while the envelope steps hold, if there IS an in-S_in effect,
  the claim is NECESSARILY emitted. "No in-scope effect goes unreported."
\<close>

lemma silent_emission_complete:
  assumes "A2 E \<iota>" and "cst_v1_covered E \<iota>" and "var \<iota> \<in> s_in E"
      and "assum_ok" and "effect_at E \<iota> To Tc i" and "i < length Tc"
  shows "emits Dstar E \<iota> assum_ok To Tc"
  unfolding emits_def admissible_def
  using assms(2) assms(4) assms(3)
        silent_no_missed_effect[OF assms(1) assms(3) assms(5) assms(6)]
  by simp

text \<open>
  (iv) S_out is OUT OF SCOPE: A2's guard is `var \<iota> \<in> s_in E`. If the guard is not
  met, A2_manifests yields NOTHING -- i.e. CST stays silent about effects that
  materialize via S_out, and this is not a SOUNDNESS claim but a SCOPE statement.
  Below we show that when no claim is emitted there is no observable
  divergence either (scope-honest silence).
\<close>

lemma scope_honest_silence:
  "\<not> diverges Dstar To Tc \<Longrightarrow> \<not> emits Dstar E \<iota> assum_ok To Tc"
  using emits_implies_divergence by blast


subsection \<open>6.16 Silent-leak class = scope boundary (step i)\<close>

text \<open>
  MI's sub-Delta* silent-leak class (extp.tex sec:mi; sec:cst Threat 2): do(x')
  can produce an effect that fires NO clause on the observable surface. The paper
  calls these "explicitly deferred to a future CMD property class". Here we turn
  that statement from PROSE into a PROVED SCOPE BOUNDARY:

    Under A2, a silent leak INSIDE S_in is IMPOSSIBLE; hence every silent leak
    is NECESSARILY in S_out (var iota ∉ s_in E). I.e. CST's scope boundary is
    not merely declared, it is ENFORCED by the assumption structure.

  Silent leak = an effect exists, but BOTH clauses of D are silent.
\<close>

definition silent_leak :: "trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool" where
  "silent_leak To Tc i \<longleftrightarrow> \<not> soe_clause To Tc i \<and> \<not> timing_clause Dstar To Tc i"

lemma silent_leak_iff_not_D: "silent_leak To Tc i \<longleftrightarrow> \<not> D Dstar To Tc i"
  by (auto simp: silent_leak_def D_def)

text \<open>(i.1) A2 FORBIDS a silent leak INSIDE S_in (in the event of the effect itself).\<close>

lemma A2_forbids_inscope_silent_leak:
  assumes "A2 E \<iota>" "var \<iota> \<in> s_in E"
      and "effect_at E \<iota> To Tc i" and "silent_leak To Tc i"
  shows False
proof -
  from A2_manifests[OF assms(1) assms(2) assms(3)] have "D Dstar To Tc i" .
  with assms(4) show False by (simp add: silent_leak_iff_not_D)
qed

text \<open>(i.2) MAIN RESULT: every silent leak is NECESSARILY out of scope (S_out).\<close>

theorem silent_leak_only_out_of_scope:
  assumes "A2 E \<iota>" and "effect_at E \<iota> To Tc i" and "silent_leak To Tc i"
  shows "var \<iota> \<notin> s_in E"
  using A2_forbids_inscope_silent_leak[OF assms(1) _ assms(2,3)] by blast

text \<open>
  (i.3) Contrapositive: if the effect is in S_in and A2 holds, that effect CANNOT
  BE SILENT -- at least one clause of D fires (it must be observable).
\<close>

corollary inscope_effect_is_observable:
  assumes "A2 E \<iota>" "var \<iota> \<in> s_in E" "effect_at E \<iota> To Tc i"
  shows "soe_clause To Tc i \<or> timing_clause Dstar To Tc i"
  using A2_manifests[OF assms] by (simp add: D_def)


subsection \<open>6.2 HP witness construction (App A item iv) -- proved\<close>

text \<open>
  W = S_in \ eff_vars (App A: "W = S_in \ observable(.)_i"). The probability of
  violating the W2 (fixity-does-not-mask) condition = mask_prob = p_soe + p_conf,
  tied to the residual via the union bound.
\<close>

definition witness_W :: "envelope \<Rightarrow> nat set" where
  "witness_W E = s_in E - eff_vars E"

definition mask_prob :: "envelope \<Rightarrow> intervention \<Rightarrow> real" where
  "mask_prob E \<iota> = p_soe E \<iota> + p_conf E \<iota>"

lemma witness_W_subset: "witness_W E \<subseteq> s_in E"
  by (simp add: witness_W_def)

\<comment> \<open>W2 union bound: masking probability <= residual\<close>
lemma w2_residual_bound:
  assumes "A1 E \<iota>" "A4 E \<iota>"
  shows "mask_prob E \<iota> \<le> residual"
  using coincidence_soe_bound[OF assms(2)] confounder_bound[OF assms(1)]
  unfolding mask_prob_def residual_def by linarith

lemma mask_prob_nonneg:
  assumes "A1 E \<iota>" "A4 E \<iota>"
  shows "0 \<le> mask_prob E \<iota>"
  using A4_bounds_soe[OF assms(2)] A1_bounds_conf[OF assms(1)]
  unfolding mask_prob_def by linarith


subsection \<open>6.3 Pearl/HP correspondence predicates -- concrete\<close>

text \<open>
  Effectiveness is now the top-level \<open>effective\<close> of §3.1 (do-operator semantics);
  the \<open>True\<close> placeholder has been removed. Here only the composition/AC predicates.
\<close>

\<comment> \<open>delta_A1-relaxed composition: in-framework perturbation bounded by delta_A1+alpha\<close>
definition composition_relaxed :: "envelope \<Rightarrow> intervention \<Rightarrow> bool" where
  "composition_relaxed E \<iota> \<longleftrightarrow> p_conf E \<iota> \<le> delta_A1 + alpha"

\<comment> \<open>HP AC1: the effect D is present at event i in Tcf\<close>
definition ac1 :: "trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool" where
  "ac1 To Tc i \<longleftrightarrow> D Dstar To Tc i"

\<comment> \<open>HP AC2(a): counterfactual sensitivity -- D's fourth admissibility step\<close>
definition ac2a :: "trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool" where
  "ac2a To Tc i \<longleftrightarrow> D Dstar To Tc i"

\<comment> \<open>WITNESS-INDEXED form of AC2(a) (App A: "each independently witness")\<close>
definition ac2a_wit :: "ac2a_witness \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool" where
  "ac2a_wit w To Tc i \<longleftrightarrow> witnesses w Dstar To Tc i"

lemma ac2a_iff_wit: "ac2a To Tc i \<longleftrightarrow> (\<exists>w. ac2a_wit w To Tc i)"
  unfolding ac2a_def ac2a_wit_def by (rule D_iff_witness)

\<comment> \<open>HP AC2(b): W1 (fixity via A4) + W ⊆ S_in + W2 (mask <= residual)\<close>
definition ac2b :: "envelope \<Rightarrow> intervention \<Rightarrow> bool" where
  "ac2b E \<iota> \<longleftrightarrow> A4 E \<iota> \<and> witness_W E \<subseteq> s_in E \<and> mask_prob E \<iota> \<le> residual"

lemma composition_relaxed_holds:
  assumes "A1 E \<iota>" shows "composition_relaxed E \<iota>"
  unfolding composition_relaxed_def using confounder_bound[OF assms] by simp

lemma ac2b_holds:
  assumes "A1 E \<iota>" "A4 E \<iota>" shows "ac2b E \<iota>"
  unfolding ac2b_def
  using assms(2) witness_W_subset w2_residual_bound[OF assms(1) assms(2)] by simp


subsection \<open>6.35 PER-WITNESS error envelope -- NEW analytic content\<close>

text \<open>
  The paper's "OR-clause asymmetry" (CST doc sec:2.1): the SOE clause is
  DETERMINISTIC (zero FPR under A4), the timing clause is PROBABILISTIC
  (FPR <= alpha). From this follows a result NOT EXPLICITLY DERIVED in the
  paper's prose:

    The epistemic weight of a claim DEPENDS ON WHICH WITNESS fired.

  Instead of the blanket `residual` we define a per-witness envelope:
    - Structural witness: coincidence contribution p_soe (<= eps_SOE by A4)
    - Timing witness:     coincidence contribution p_tim (<= alpha by A3)
  Both additionally receive the confounder contribution p_conf (<= delta_A1 + alpha).
\<close>

definition wit_bound :: "ac2a_witness \<Rightarrow> envelope \<Rightarrow> intervention \<Rightarrow> real" where
  "wit_bound w E \<iota> =
     (case w of StructuralW \<Rightarrow> p_soe E \<iota> + p_conf E \<iota>
              | TimingW     \<Rightarrow> p_tim E \<iota> + p_conf E \<iota>)"

lemma wit_bound_structural:
  assumes "A1 E \<iota>" "A4 E \<iota>"
  shows "wit_bound StructuralW E \<iota> \<le> eps_SOE + delta_A1 + alpha"
  using coincidence_soe_bound[OF assms(2)] confounder_bound[OF assms(1)]
  unfolding wit_bound_def by simp

lemma wit_bound_timing:
  assumes "A1 E \<iota>" "A3 E \<iota>"
  shows "wit_bound TimingW E \<iota> \<le> delta_A1 + 2 * alpha"
  using coincidence_timing_bound[OF assms(2)] confounder_bound[OF assms(1)]
  unfolding wit_bound_def by simp

text \<open>The structural witness's envelope is exactly App A's `residual`.\<close>

lemma wit_bound_structural_is_residual:
  assumes "A1 E \<iota>" "A4 E \<iota>"
  shows "wit_bound StructuralW E \<iota> \<le> residual"
  using wit_bound_structural[OF assms] unfolding residual_def by simp

text \<open>
  MAIN RESULT: which witness yields the TIGHTER envelope? The exact comparison
  criterion is the relation between eps_SOE and alpha -- it depends on no other parameter.
\<close>

lemma structural_bound_tighter_iff:
  "(eps_SOE + delta_A1 + alpha \<le> delta_A1 + 2 * alpha) \<longleftrightarrow> eps_SOE \<le> alpha"
  by simp

text \<open>
  Reading (with the paper's calibration regimes):
    - WITHIN-BOOT (N=998): eps_SOE <= 0.37%, alpha_realized = 0.61%
      => eps_SOE <= alpha  => the STRUCTURAL witness yields the tighter envelope.
    - CROSS-BOOT (N=34):   eps_SOE <= 10.4%, alpha_realized = 0.61%
      => eps_SOE > alpha   => the criterion FLIPS; the timing witness is tighter.
  So the answer to "which witness is stronger" depends on the calibration regime,
  and this is characterized exactly by a single inequality.
\<close>


subsection \<open>6.4 Conditional CST theorem (Theorem 1, => direction) -- proved\<close>

theorem cst_conditional:
  assumes A1h: "A1 E \<iota>" and A2h: "A2 E \<iota>" and A3h: "A3 E \<iota>" and A4h: "A4 E \<iota>"
      and align: "aligned To Tc"
      and adm: "admissible Dstar E \<iota> assum_ok To Tc"
  shows "effective \<iota>
       \<and> composition_relaxed E \<iota>
       \<and> (\<exists>i w. i < length Tc \<and> i < length To
            \<and> D Dstar To Tc i
            \<and> ac1 To Tc i
            \<and> ac2a To Tc i
            \<and> ac2a_wit w To Tc i
            \<and> ac2b E \<iota>
            \<and> wit_bound w E \<iota> \<le> max (eps_SOE + delta_A1 + alpha)
                                     (delta_A1 + 2 * alpha))"
proof -
  from adm have "diverges Dstar To Tc" by (simp add: admissible_def)
  then obtain i where i: "i < length Tc" "D Dstar To Tc i"
    by (auto simp: diverges_def)
  from align i(1) have iTo: "i < length To" by (rule aligned_index_safe)
  \<comment> \<open>extract a concrete AC2(a) witness from D\<close>
  from i(2) obtain w where w: "witnesses w Dstar To Tc i"
    using D_iff_witness by blast
  \<comment> \<open>a witness's own envelope is bounded by the maximum of the two witness envelopes\<close>
  have wb: "wit_bound w E \<iota> \<le> max (eps_SOE + delta_A1 + alpha) (delta_A1 + 2 * alpha)"
  proof (cases w)
    case StructuralW
    then show ?thesis using wit_bound_structural[OF A1h A4h] by simp
  next
    case TimingW
    then show ?thesis using wit_bound_timing[OF A1h A3h] by simp
  qed
  have "effective \<iota>" by (rule effective_holds)
  moreover have "composition_relaxed E \<iota>" using composition_relaxed_holds[OF A1h] .
  moreover have "ac1 To Tc i" using i(2) by (simp add: ac1_def)
  moreover have "ac2a To Tc i" using i(2) by (simp add: ac2a_def)
  moreover have "ac2a_wit w To Tc i" using w by (simp add: ac2a_wit_def)
  moreover have "ac2b E \<iota>" using ac2b_holds[OF A1h A4h] .
  ultimately show ?thesis using i iTo wb by blast
qed

text \<open>
  We additionally show that the residual envelope lies in the interval
  [0, residual] reported with every admissible claim (App A: "reported per-claim").
\<close>

corollary cst_residual_reported:
  assumes "A1 E \<iota>" "A4 E \<iota>"
  shows "0 \<le> mask_prob E \<iota> \<and> mask_prob E \<iota> \<le> residual"
  using mask_prob_nonneg[OF assms] w2_residual_bound[OF assms] by simp


subsection \<open>6.45 SCOPE-COMPLETENESS theorem -- A2's real job\<close>

text \<open>
  CST has two SEPARATE sufficiency directions; it is important not to conflate them:

    SOUNDNESS      (cst_conditional):   published claims are sound.
                                        Uses: A1, A3, A4.
    SCOPE-COMPLETENESS (below):         effects inside S_in are NOT MISSED.
                                        Uses: A2.

  This is why A2 appears in the hypothesis list of cst_conditional yet is never
  invoked in its proof -- A2 contributes to COMPLETENESS, not to SOUNDNESS.
  Stating it as a separate theorem removes the appearance of A2 being a "dead
  hypothesis" and pins down its role.
\<close>

theorem cst_scope_complete:
  assumes A2h: "A2 E \<iota>"
      and cov: "cst_v1_covered E \<iota>"
      and inscope: "var \<iota> \<in> s_in E"
      and refs: "assum_ok"
      and eff: "effect_at E \<iota> To Tc i"
      and idx: "i < length Tc"
  shows "emits Dstar E \<iota> assum_ok To Tc \<and> (\<exists>j < length Tc. D Dstar To Tc j)"
proof
  show "emits Dstar E \<iota> assum_ok To Tc"
    by (rule silent_emission_complete[OF A2h cov inscope refs eff idx])
next
  from A2_manifests[OF A2h inscope eff] idx
  show "\<exists>j < length Tc. D Dstar To Tc j" by blast
qed

text \<open>
  Contrapositive reading (scope-honesty): if there is no divergence at all, there
  is NO causal effect inside S_in either. So CST's silence is informative over
  S_in -- and says NOTHING over S_out.
\<close>

corollary silence_informative_over_s_in:
  assumes "A2 E \<iota>" and "var \<iota> \<in> s_in E"
      and "\<not> diverges Dstar To Tc" and "i < length Tc"
  shows "\<not> effect_at E \<iota> To Tc i"
proof
  assume "effect_at E \<iota> To Tc i"
  from silent_no_missed_effect[OF assms(1) assms(2) this assms(4)]
  have "diverges Dstar To Tc" .
  with assms(3) show False by simp
qed


subsection \<open>6.5 Sequential composition (Proposition 1) -- proved\<close>

text \<open>
  App A Proposition 1: an n-step chain is admissible <=> every atomic step is
  admissible; delta_A1 accumulates by union bound (O(n), no degradation). We model
  the chain as the list of per-step admissibility booleans.
\<close>

\<comment> \<open>Chain admissible <=> all atomic steps admissible (App A induction, biconditional)\<close>
lemma chain_iff_all_atomic:
  "list_all (\<lambda>b. b) steps \<longleftrightarrow> (\<forall>k < length steps. steps ! k)"
  by (simp add: list_all_length)

\<comment> \<open>accumulated delta_A1 envelope after n steps\<close>
primrec accum_delta :: "nat \<Rightarrow> real" where
  "accum_delta 0 = 0"
| "accum_delta (Suc n) = accum_delta n + delta_A1"

lemma accum_delta_eq: "accum_delta n = of_nat n * delta_A1"
  by (induct n) (simp_all add: algebra_simps)

\<comment> \<open>Union bound: the envelope grows linearly in the number of steps, monotone -- no degradation\<close>
lemma accum_delta_mono: "accum_delta n \<le> accum_delta (Suc n)"
  using prob_nonneg(1) by simp

lemma accum_delta_linear_bound: "accum_delta n \<le> of_nat n * delta_A1"
  by (simp add: accum_delta_eq)


subsection \<open>6.55 Parallel sweep: WITNESS-SENSITIVE ensemble envelope (b x Prop 1)\<close>

text \<open>
  CAUTION -- axis distinction. accum_delta (above) is the delta_A1 union-bound
  accumulation of SEQUENTIAL composition (Prop 1). This subsection is for the
  PARALLEL sweep instead: App A "Scope clarification: sequential vs parallel
  ensembles" -- sweep = 33 INDEPENDENT atomic claims, each verified separately
  against Korig, delta_A1 bounded per-claim, NO union-bound accumulation over i,
  scope O(n).

  Step (b) showed that each claim's envelope depends on the WITNESS THAT FIRED.
  In a sweep, different claims may fire on different witnesses; hence the
  ensemble-level (total) envelope must be WITNESS-SENSITIVE and is TIGHTER than
  the naive "n * blanket" bound. That is exactly what carrying (b) over to the
  sweep amounts to.
\<close>

definition wit_ub :: "ac2a_witness \<Rightarrow> real" where
  "wit_ub w = (case w of StructuralW \<Rightarrow> eps_SOE + delta_A1 + alpha
                       | TimingW     \<Rightarrow> delta_A1 + 2 * alpha)"

definition blanket :: real where
  "blanket = max (eps_SOE + delta_A1 + alpha) (delta_A1 + 2 * alpha)"

definition sweep_ub :: "ac2a_witness list \<Rightarrow> real" where
  "sweep_ub ws = sum_list (map wit_ub ws)"

lemma wit_ub_le_blanket: "wit_ub w \<le> blanket"
  by (cases w) (simp_all add: wit_ub_def blanket_def)

lemma sweep_ub_singleton_struct: "sweep_ub [StructuralW] = eps_SOE + delta_A1 + alpha"
  by (simp add: sweep_ub_def wit_ub_def)

lemma sweep_ub_singleton_timing: "sweep_ub [TimingW] = delta_A1 + 2 * alpha"
  by (simp add: sweep_ub_def wit_ub_def)

lemma wit_ub_nonneg: "0 \<le> wit_ub w"
  using prob_nonneg by (cases w) (simp_all add: wit_ub_def)

lemma sum_list_const_real:
  "sum_list (map (\<lambda>_. (c::real)) ws) = of_nat (length ws) * c"
  by (induct ws) (simp_all add: algebra_simps)

primrec countS :: "ac2a_witness list \<Rightarrow> nat" where
  "countS [] = 0"
| "countS (w # ws) = (if w = StructuralW then 1 else 0) + countS ws"

primrec countT :: "ac2a_witness list \<Rightarrow> nat" where
  "countT [] = 0"
| "countT (w # ws) = (if w = TimingW then 1 else 0) + countT ws"

lemma length_countS_countT: "length ws = countS ws + countT ws"
proof (induct ws)
  case Nil show ?case by simp
next
  case (Cons w ws) thus ?case by (cases w) simp_all
qed

text \<open>Closed form: k structural + (n-k) timing witnesses.\<close>

lemma sweep_ub_closed_form:
  "sweep_ub ws = of_nat (countS ws) * (eps_SOE + delta_A1 + alpha)
               + of_nat (countT ws) * (delta_A1 + 2 * alpha)"
proof (induct ws)
  case Nil show ?case by (simp add: sweep_ub_def)
next
  case (Cons w ws) thus ?case
    by (cases w) (simp_all add: sweep_ub_def wit_ub_def algebra_simps)
qed

text \<open>MAIN RESULT: the witness-sensitive envelope is TIGHTER than naive blanket accumulation.\<close>

lemma sweep_ub_tighter:
  "sweep_ub ws \<le> of_nat (length ws) * blanket"
proof -
  have "sweep_ub ws = sum_list (map wit_ub ws)" by (simp add: sweep_ub_def)
  also have "\<dots> \<le> sum_list (map (\<lambda>_. blanket) ws)"
    by (intro sum_list_mono) (rule wit_ub_le_blanket)
  also have "\<dots> = of_nat (length ws) * blanket" by (rule sum_list_const_real)
  finally show ?thesis .
qed

lemma sweep_ub_nonneg: "0 \<le> sweep_ub ws"
  unfolding sweep_ub_def by (intro sum_list_nonneg) (auto simp: wit_ub_nonneg)

text \<open>
  The REAL contribution bridge: each step's measured envelope (wit_bound) is below
  its own witness upper bound (wit_ub); hence the ensemble's measured total
  envelope is bounded by the witness-sensitive sweep_ub. Three tiers: measured <=
  witness-counted <= naive blanket.
\<close>

lemma wit_bound_le_ub:
  assumes "A1 E \<iota>" "A3 E \<iota>" "A4 E \<iota>"
  shows "wit_bound w E \<iota> \<le> wit_ub w"
proof (cases w)
  case StructuralW
  then show ?thesis
    using wit_bound_structural[OF assms(1) assms(3)] by (simp add: wit_ub_def)
next
  case TimingW
  then show ?thesis
    using wit_bound_timing[OF assms(1) assms(2)] by (simp add: wit_ub_def)
qed

definition sweep_actual :: "envelope \<Rightarrow> intervention \<Rightarrow> ac2a_witness list \<Rightarrow> real" where
  "sweep_actual E \<iota> ws = sum_list (map (\<lambda>w. wit_bound w E \<iota>) ws)"

lemma sweep_actual_le_ub:
  assumes "A1 E \<iota>" "A3 E \<iota>" "A4 E \<iota>"
  shows "sweep_actual E \<iota> ws \<le> sweep_ub ws"
  unfolding sweep_actual_def sweep_ub_def
  by (intro sum_list_mono) (rule wit_bound_le_ub[OF assms])

text \<open>The three-tier bound in a single statement.\<close>

theorem sweep_three_level_bound:
  assumes "A1 E \<iota>" "A3 E \<iota>" "A4 E \<iota>"
  shows "sweep_actual E \<iota> ws \<le> sweep_ub ws
       \<and> sweep_ub ws \<le> of_nat (length ws) * blanket"
  using sweep_actual_le_ub[OF assms] sweep_ub_tighter by blast

text \<open>
  SILENT INPUTS ARE FREE: the ensemble envelope scales only with the number of
  ADMISSIBLE claims, NOT with the TOTAL number of swept inputs. This is the
  ensemble-level consequence of scope-honesty (d) -- D=false inputs (None) never
  enter the envelope.
\<close>

lemma ensemble_envelope_bound:
  "sweep_ub (emitted_of xs) \<le> of_nat (length (emitted_of xs)) * blanket"
  by (rule sweep_ub_tighter)

lemma silent_inputs_free:
  "sweep_ub (emitted_of (None # xs)) = sweep_ub (emitted_of xs)"
  by simp

end  \<comment> \<open>locale cst_assumptions\<close>


subsection \<open>6.6 Locale consistency: an interpretation\<close>

text \<open>
  We show that the locale is CONSISTENT (non-contradictory) by a concrete
  interpretation satisfying its assumptions: all contributions 0, all bounds at
  mid-range values. This confirms that it is not "vacuously true" and that the
  theorems hold in an actual model.
\<close>

interpretation cst_trivial:
  cst_assumptions
    500                              \<comment> \<open>Dstar\<close>
    "1/10" "1/10" "1/20"             \<comment> \<open>delta_A1, eps_SOE, alpha\<close>
    "\<lambda>E \<iota>. True" "\<lambda>E \<iota>. True"         \<comment> \<open>A1, A2\<close>
    "\<lambda>E \<iota>. True" "\<lambda>E \<iota>. True"         \<comment> \<open>A3, A4\<close>
    "\<lambda>E \<iota>. 0" "\<lambda>E \<iota>. 0" "\<lambda>E \<iota>. 0"     \<comment> \<open>p_soe, p_tim, p_conf\<close>
    "\<lambda>E. {}"                         \<comment> \<open>eff_vars\<close>
    "\<lambda>E \<iota> To Tc i. soe_clause To Tc i"   \<comment> \<open>effect_at: effects are reflected STRUCTURALLY (NOT vacuous)\<close>
  by unfold_locales (auto simp: D_def)


subsection \<open>6.7 The paper's ACTUAL calibration regimes -- numerical instantiation\<close>

text \<open>
  We instantiate the witness-comparison criterion above (structural_bound_tighter_iff)
  with the calibration values the paper REPORTS.
  Thus the mechanization does not stay abstract but ties directly to the numbers in extp.tex.

  Source: extp.tex sec:capsep / sec:soe / sec:mi
    Dstar        = 9077 cycle   (1.645 * 5518; L1-pchase / S1, boot_log12)
    within-boot  : eps_SOE, delta_A1 <= 0.37%  (N=998),  alpha = 0.61% (boot_log8)
    cross-boot   : eps_SOE, delta_A1 <= 10.4%  (N=34),   alpha = 0.61%
\<close>

interpretation cst_withinboot:
  cst_assumptions
    9077
    "37/10000" "37/10000" "61/10000"     \<comment> \<open>delta_A1, eps_SOE, alpha\<close>
    "\<lambda>E \<iota>. True" "\<lambda>E \<iota>. True" "\<lambda>E \<iota>. True" "\<lambda>E \<iota>. True"
    "\<lambda>E \<iota>. 0" "\<lambda>E \<iota>. 0" "\<lambda>E \<iota>. 0"
    "\<lambda>E. {}"
    "\<lambda>E \<iota> To Tc i. soe_clause To Tc i"   \<comment> \<open>effect_at: effects are reflected STRUCTURALLY (NOT vacuous)\<close>
  by unfold_locales (auto simp: D_def)

interpretation cst_crossboot:
  cst_assumptions
    9077
    "1040/10000" "1040/10000" "61/10000"
    "\<lambda>E \<iota>. True" "\<lambda>E \<iota>. True" "\<lambda>E \<iota>. True" "\<lambda>E \<iota>. True"
    "\<lambda>E \<iota>. 0" "\<lambda>E \<iota>. 0" "\<lambda>E \<iota>. 0"
    "\<lambda>E. {}"
    "\<lambda>E \<iota> To Tc i. soe_clause To Tc i"   \<comment> \<open>effect_at: effects are reflected STRUCTURALLY (NOT vacuous)\<close>
  by unfold_locales (auto simp: D_def)

text \<open>
  WITHIN-BOOT: eps_SOE (0.37%) <= alpha (0.61%)  =>  the STRUCTURAL witness is tighter.
  Envelopes: structural 1.35%  vs  timing 1.59%.
\<close>

lemma withinboot_criterion: "(37/10000 :: real) \<le> 61/10000"
  by simp

lemma withinboot_structural_tighter:
  "(37/10000 :: real) + 37/10000 + 61/10000 \<le> 37/10000 + 2 * (61/10000)"
  by simp

text \<open>
  CROSS-BOOT: eps_SOE (10.4%) > alpha (0.61%)  =>  the criterion FLIPS,
  the TIMING witness is tighter. Envelopes: structural 21.41%  vs  timing 11.62%.
\<close>

lemma crossboot_criterion: "\<not> ((1040/10000 :: real) \<le> 61/10000)"
  by simp

lemma crossboot_timing_tighter:
  "(1040/10000 :: real) + 2 * (61/10000) \<le> 1040/10000 + 1040/10000 + 61/10000"
  by simp

text \<open>
  That these two regimes give OPPOSITE outcomes takes the witness distinction out
  of the cosmetic: the epistemic weight of a CST claim depends both on WHICH
  WITNESS fired and on WHICH CALIBRATION REGIME one operates in. Downstream
  consumers (mitigation verification, counterfactual fuzzing) can report a
  tighter -- and, in the right regime, more HONEST -- bound by using the
  per-witness envelope instead of the blanket `residual`.
\<close>


subsection \<open>6.75 Mixed sweep: witness-sensitive envelope STRICTLY tighter (numerical)\<close>

text \<open>
  The concrete payoff of (f): in the within-boot regime, for a 2-claim sweep with
  one claim fired by the structural and one by the timing witness, the
  witness-sensitive total envelope is 2.94%, whereas the naive "n * blanket" gives
  3.18% -- i.e. STRICTLY tighter (not equal). In the end-to-end coverage map of an
  S1/T1 sweep (paper Fig. sweep) this gap grows in proportion to the number of claims.
\<close>

lemma withinboot_sweep_strictly_tighter:
  "cst_withinboot.sweep_ub [StructuralW, TimingW]
     < of_nat (length [StructuralW, TimingW]) * cst_withinboot.blanket"
  by (simp add: cst_withinboot.sweep_ub_def cst_withinboot.wit_ub_def
                cst_withinboot.blanket_def)

text \<open>Closed-form check: sweep_ub [S,T] = 294/10000.\<close>

lemma withinboot_sweep_value:
  "cst_withinboot.sweep_ub [StructuralW, TimingW] = 294/10000"
  by (simp add: cst_withinboot.sweep_ub_def cst_withinboot.wit_ub_def)

text \<open>Naive blanket accumulation = 318/10000; difference = 24/10000 (~0.12% per claim).\<close>

lemma withinboot_blanket_value:
  "of_nat (length [StructuralW, TimingW]) * cst_withinboot.blanket = 318/10000"
  by (simp add: cst_withinboot.blanket_def)

text \<open>
  Equality in a homogeneous sweep: if all claims fire on the same (worst) witness,
  the witness-sensitive envelope EQUALS the naive blanket -- i.e. the tightness
  gain comes exactly from the witness MIX, and from nowhere else.
\<close>

lemma withinboot_homogeneous_equality:
  "cst_withinboot.sweep_ub [TimingW, TimingW]
     = of_nat (length [TimingW, TimingW]) * cst_withinboot.blanket"
  by (simp add: cst_withinboot.sweep_ub_def cst_withinboot.wit_ub_def
                cst_withinboot.blanket_def)


subsection \<open>6.8 Tying to the REAL sweep data (step h)\<close>

text \<open>
  The actual result of extp.tex sec:eval-demo-sweep:
    - 33 inputs swept (0xDEAD + 16 low-byte + 14 wide + 2 distractor).
    - Divergence count 1/33: only 0xDEAD fired (SOE clause; RIP 0x10016,
      RAX 0x80000008). The other 32 are default-path, SOE clause SILENT => D=false
      => NO ADMISSIBLE CLAIM.
    - All divergence is SOE-clause; the TIMING witness never fires.
  We encode this into the model verbatim.
\<close>

definition dead_sweep :: "ac2a_witness option list" where
  "dead_sweep = Some StructuralW # replicate 32 None"

lemma dead_sweep_total: "length dead_sweep = 33"
  by (simp add: dead_sweep_def)

lemma dead_sweep_emitted: "emitted_of dead_sweep = [StructuralW]"
  by (simp add: dead_sweep_def emitted_of_def filter_replicate)

lemma dead_sweep_emitted_count: "length (emitted_of dead_sweep) = 1"
  by (simp add: dead_sweep_emitted)

text \<open>
  The ensemble envelope, with the REAL calibration. WITHIN-BOOT: only 1 structural claim
  => envelope = eps_SOE + delta_A1 + alpha = 1.35%.
\<close>

lemma dead_sweep_envelope_withinboot:
  "cst_withinboot.sweep_ub (emitted_of dead_sweep) = 135/10000"
  apply (subst dead_sweep_emitted)
  apply (subst cst_withinboot.sweep_ub_singleton_struct)
  apply simp
  done

lemma dead_sweep_envelope_crossboot:
  "cst_crossboot.sweep_ub (emitted_of dead_sweep) = 2141/10000"
  apply (subst dead_sweep_emitted)
  apply (subst cst_crossboot.sweep_ub_singleton_struct)
  apply simp
  done

text \<open>Naive swept-input bound = 33 * 1.59% = 52.47%.\<close>

lemma dead_sweep_naive_swept_value:
  "of_nat (length dead_sweep) * cst_withinboot.blanket = 5247/10000"
  by (simp add: dead_sweep_total cst_withinboot.blanket_def)

text \<open>
  Concrete silent leak: the +400-cycle difference in ex_silent is sub-threshold under
  the real Delta*=9077 (within-boot) => both clauses silent => silent_leak. (step i, concrete link)
\<close>

lemma ex_silent_is_silent_leak_withinboot:
  "cst_withinboot.silent_leak ex_orig ex_silent 0"
  by (simp add: cst_withinboot.silent_leak_def soe_clause_def timing_clause_def
                ex_orig_def ex_silent_def ev_def)

text \<open>
  Hence (with silent_leak_only_out_of_scope): such a sub-Delta* effect can, under A2,
  live only in S_out -- the machine-checked core of deferring MI's silent-leak class
  to the CMD future class.
\<close>

text \<open>
  MAIN RESULT (scope-honesty x ensemble): the envelope of the 33-input sweep scales
  with the number of admissible claims (1), NOT with the number of swept inputs. The
  naive view "every swept input carries a load" would give 33 * blanket = 52.47%; the
  actual envelope is 1.35% -- ~39x tighter, because the 32 silent inputs are FREE.
\<close>

lemma dead_sweep_envelope_vs_naive_swept:
  "cst_withinboot.sweep_ub (emitted_of dead_sweep)
     < of_nat (length dead_sweep) * cst_withinboot.blanket"
  using dead_sweep_envelope_withinboot dead_sweep_naive_swept_value by simp


section \<open>7. PHASE 3 interface skeleton (lifting) -- OBLIGATION ISOLATED, GAP NOT CLOSED\<close>

text \<open>
  >>> HONESTY NOTE (critical). This section does NOT close the lifting gap. Actually
  closing it requires hooking into L4.verified's enormous Isabelle proof and
  formalizing the VMM/VT-x layer (multi-year; and covering K_verified only).
  What is done here: (1) define the TYPED INTERFACE of the lifting; (2) ISOLATE the
  SINGLE theorem seL4 must supply -- external atomicity of K_verified
  operations -- as an explicit, NAMED locale ASSUMPTION; (3) prove that, GIVEN
  this assumption, A1 follows structurally for K_verified with delta_A1=0
  (unconditional modularity); (4) show that K_extended falls outside this
  assumption's guard and therefore remains empirical. The assumption is NOT
  PROVED -- the multi-year hole is exactly there; we do not close it, we reduce it
  to a SINGLE, marked obligation and fence it off.
\<close>

typedecl sel4_astate   \<comment> \<open>seL4 abstract machine state (opaque; the real model lives in L4.verified)\<close>

consts
  lift :: "sel4_astate \<Rightarrow> observable"   \<comment> \<open>abstract state -> EXTp VMCS-observable surface\<close>

datatype kop =
    Create | Copy | Revoke | Destroy        \<comment> \<open>K_verified (within L4.verified scope)\<close>
  | MapEPT | Unmap | ReadVMCS | WriteVMCS    \<comment> \<open>K_extended (OUTSIDE verified scope)\<close>

definition k_verified :: "kop set" where
  "k_verified = {Create, Copy, Revoke, Destroy}"

definition k_extended :: "kop set" where
  "k_extended = {MapEPT, Unmap, ReadVMCS, WriteVMCS}"

lemma k_partition_disjoint: "k_verified \<inter> k_extended = {}"
  by (auto simp: k_verified_def k_extended_def)

lemma k_partition_complete: "k_verified \<union> k_extended = UNIV"
  by (auto simp: k_verified_def k_extended_def) (case_tac x, auto)

text \<open>
  seL4 interface locale. `op_authority op` = the set of variables that op can touch;
  `fwk_vars` = the framework-internal (K_fwk) variables. Single assumption:
  K_verified ops DO NOT touch framework-internal state (the operational counterpart
  of external atomicity). This is what L4.verified PROVIDES; it is NOT PROVED HERE.
\<close>

locale sel4_lifting =
  fixes op_authority :: "kop \<Rightarrow> nat set"
    and fwk_vars      :: "nat set"
  assumes verified_no_fwk_touch:
    "\<And>op. op \<in> k_verified \<Longrightarrow> op_authority op \<inter> fwk_vars = {}"
    \<comment> \<open>^ L4.verified external-atomicity obligation; OPEN, the single hole.\<close>
begin

text \<open>
  (g.1) Given the assumption, the UNCONDITIONAL form of A1 for K_verified (delta=0):
  if the intervention is a K_verified op, it CANNOT affect framework-internal state.
\<close>

theorem A1_unconditional_for_verified:
  assumes "op \<in> k_verified"
  shows "op_authority op \<inter> fwk_vars = {}"
  by (rule verified_no_fwk_touch[OF assms])

corollary verified_no_confounder:
  assumes "op \<in> k_verified" and "v \<in> fwk_vars"
  shows "v \<notin> op_authority op"
  using A1_unconditional_for_verified[OF assms(1)] assms(2) by blast

text \<open>
  (g.2) K_extended lies OUTSIDE the assumption's guard: this locale says NOTHING
  about it. A world in which such an op touches the framework is CONSISTENT
  (interpretation below) -- i.e. delta=0 does NOT follow for K_extended; it stays
  empirical. This is the machine-checked counterpart of the paper's K_verified
  (unconditional) / K_extended (empirical) distinction.
\<close>

lemma verified_guard_excludes_extended:
  "MapEPT \<notin> k_verified"
  by (simp add: k_verified_def)

end  \<comment> \<open>locale sel4_lifting\<close>

text \<open>
  (g.3) CONSISTENCY + PROOF that K_extended is not covered: there is an interpretation
  such that (a) the assumption holds (the locale is non-empty), (b) some K_extended
  op DOES touch the framework. So the interface is consistent BUT does not rescue
  K_extended.
\<close>

definition demo_auth :: "kop \<Rightarrow> nat set" where
  "demo_auth op = (if op \<in> k_verified then {} else {0})"

interpretation sel4_demo:
  sel4_lifting demo_auth "{0}"
  by unfold_locales (simp add: demo_auth_def)

lemma extended_can_touch_fwk:
  "demo_auth MapEPT \<inter> {0} \<noteq> {}"    \<comment> \<open>K_extended touches the framework\<close>
  by (simp add: demo_auth_def k_verified_def k_extended_def)

lemma verified_cannot_touch_fwk:
  "demo_auth Create \<inter> {0} = {}"      \<comment> \<open>K_verified does not\<close>
  by (simp add: demo_auth_def k_verified_def)

text \<open>
  >>> SUMMARY. The theorems above do NOT close the lifting. Closing it =
  DERIVING the `verified_no_fwk_touch` assumption from L4.verified's actual atomicity
  theorem (and connecting `lift`/`sel4_astate` to the real seL4 machine model). That
  work is NOT in this file and is multi-year. Here only: the obligation has been made
  single and named, its consequences (K_verified delta=0) have been proved, and
  K_extended has been shown to remain out of scope. The conditional CST theorem (Phase 2)
  needs NONE of this section; this section merely exhibits, in typed form, the price
  tag of moving a subset of A1 out of the empirical realm.
\<close>

section \<open>8. Closing two "prose" corners: composition in W-form + trace-threaded Prop 1\<close>

text \<open>
  The statement-fidelity audit (2026-09-01) had left two points of the paper proof as "prose":
    (F2) App A item (ii): the delta_A1-relaxed form of Pearl composition is stated in the
         paper via the W variables over K_fwk and the perturbation |W_cf - W_orig|;
         the mechanization had MODELLED this only as a confounder bound
         (composition_relaxed).
    (F5) Prop 1 sequential composition: in the paper T_cf^(k) is the BASELINE of the next
         step; the mechanization carried only the n*delta_A1 arithmetic.
  This section closes both so that they correspond exactly to the paper's statements.
  The antecedent discipline is preserved: probabilities (p_pert) enter as abstract real parameters.
\<close>

subsection \<open>8.1 Holding W: the structural part (outside the locale)\<close>

text \<open>
  hold W \<sigma>o \<sigma>: in valuation \<sigma>, pins the variables in the set W to their values in T_orig
  (\<sigma>o) -- Pearl/HP's "while holding W = w_orig" operation.
\<close>

definition hold :: "nat set \<Rightarrow> valuation \<Rightarrow> valuation \<Rightarrow> valuation" where
  "hold W \<sigma>o \<sigma> = (\<lambda>v. if v \<in> W then \<sigma>o v else \<sigma> v)"

text \<open>On every W-variable |W_cf - W_orig| \<le> Dstar (App A: "perturbation bounded by Dstar on each W").\<close>

definition pert_bounded :: "nat \<Rightarrow> nat set \<Rightarrow> valuation \<Rightarrow> valuation \<Rightarrow> bool" where
  "pert_bounded Dstar W \<sigma>o \<sigma>c \<longleftrightarrow> (\<forall>w\<in>W. \<bar>int (\<sigma>c w) - int (\<sigma>o w)\<bar> \<le> int Dstar)"

lemma hold_in:  "v \<in> W \<Longrightarrow> hold W \<sigma>o \<sigma> v = \<sigma>o v" by (simp add: hold_def)
lemma hold_out: "v \<notin> W \<Longrightarrow> hold W \<sigma>o \<sigma> v = \<sigma> v" by (simp add: hold_def)

text \<open>
  Pearl composition, STRICT form: if W is already at its natural value (W_x = w), holding W
  does not change the outcome -- do(x') alone and do(x') + hold W yield the SAME valuation.
  The only structural precondition: the intervention variable lies OUTSIDE W (CapSep: K_int \<inter> K_fwk = {}).
  Otherwise hold would undo the intervention.
\<close>

lemma composition_strict_structural:
  assumes "var \<iota> \<notin> W" and "\<forall>w\<in>W. \<sigma>c w = \<sigma>o w"
  shows "hold W \<sigma>o (apply_iv \<iota> \<sigma>c) = apply_iv \<iota> \<sigma>c"
proof
  fix v
  show "hold W \<sigma>o (apply_iv \<iota> \<sigma>c) v = apply_iv \<iota> \<sigma>c v"
  proof (cases "v \<in> W")
    case True
    with assms(1) have "v \<noteq> var \<iota>" by auto
    with True assms(2) show ?thesis by (simp add: hold_def apply_iv_def)
  next
    case False then show ?thesis by (simp add: hold_def)
  qed
qed

text \<open>Effectiveness is preserved while holding W too: hold does not undo do(x').\<close>

lemma hold_preserves_effectiveness:
  assumes "var \<iota> \<notin> W"
  shows "hold W \<sigma>o (apply_iv \<iota> \<sigma>c) (var \<iota>) = newval \<iota>"
  using assms by (simp add: hold_def apply_iv_def)

text \<open>
  delta_A1-RELAXED form, structural part: even if W is NOT exactly at its natural value, the two
  do(x') outcomes with and without holding W are (a) identical outside W (including X),
  (b) different by at most Dstar on every coordinate inside W -- under pert_bounded.
\<close>

lemma composition_relaxed_structural:
  assumes "var \<iota> \<notin> W" and "pert_bounded Dstar W \<sigma>o \<sigma>c"
  shows "(\<forall>v. v \<notin> W \<longrightarrow> hold W \<sigma>o (apply_iv \<iota> \<sigma>c) v = apply_iv \<iota> \<sigma>c v)
       \<and> (\<forall>w\<in>W. \<bar>int (hold W \<sigma>o (apply_iv \<iota> \<sigma>c) w) - int (apply_iv \<iota> \<sigma>c w)\<bar> \<le> int Dstar)"
proof (intro conjI allI ballI impI)
  fix v assume "v \<notin> W"
  then show "hold W \<sigma>o (apply_iv \<iota> \<sigma>c) v = apply_iv \<iota> \<sigma>c v" by (simp add: hold_def)
next
  fix w assume w: "w \<in> W"
  with assms(1) have "w \<noteq> var \<iota>" by auto
  then have "apply_iv \<iota> \<sigma>c w = \<sigma>c w" by (simp add: apply_iv_def)
  moreover from w have "hold W \<sigma>o (apply_iv \<iota> \<sigma>c) w = \<sigma>o w" by (simp add: hold_def)
  moreover from assms(2) w have "\<bar>int (\<sigma>c w) - int (\<sigma>o w)\<bar> \<le> int Dstar"
    by (simp add: pert_bounded_def)
  ultimately show "\<bar>int (hold W \<sigma>o (apply_iv \<iota> \<sigma>c) w) - int (apply_iv \<iota> \<sigma>c w)\<bar> \<le> int Dstar"
    by (simp add: abs_minus_commute)
qed


subsection \<open>8.2 Probabilistic part: locale cst_composition (the symbolic content of A1)\<close>

text \<open>
  App A, the symbolic form of A1: for every W \<in> K_fwk, Pr[|W_cf - W_orig| > Dstar] \<le> delta_A1.
  p_pert E \<iota> w is the abstract real parameter for this probability (measured, not proved -- antecedent
  discipline). The second assumption is the intervention-variable-level form of CapSep's
  structural claim K_int \<inter> K_fwk = {}: under A1 the target X lies outside K_fwk.
\<close>

locale cst_composition = cst_assumptions +
  fixes fwk_vars :: "nat set"
    and p_pert   :: "envelope \<Rightarrow> intervention \<Rightarrow> nat \<Rightarrow> real"
  assumes A1_pert_per_var:
    "\<And>E \<iota> w. A1 E \<iota> \<Longrightarrow> w \<in> fwk_vars \<Longrightarrow> 0 \<le> p_pert E \<iota> w \<and> p_pert E \<iota> w \<le> delta_A1"
      and A1_target_outside_fwk:
    "\<And>E \<iota>. A1 E \<iota> \<Longrightarrow> var \<iota> \<notin> fwk_vars"
begin

text \<open>
  App A item (ii), verbatim as stated in the paper: "for all W in K_fwk, the outcome under
  do(x') equals the outcome under do(x') while holding W = w_orig, up to a perturbation
  bounded by Dstar on each W with probability at least 1 - delta_A1".
\<close>

definition composition_W :: "envelope \<Rightarrow> intervention \<Rightarrow> bool" where
  "composition_W E \<iota> \<longleftrightarrow>
     var \<iota> \<notin> fwk_vars
   \<and> (\<forall>w\<in>fwk_vars. p_pert E \<iota> w \<le> delta_A1)
   \<and> (\<forall>\<sigma>o \<sigma>c. pert_bounded Dstar fwk_vars \<sigma>o \<sigma>c \<longrightarrow>
        (\<forall>v. v \<notin> fwk_vars \<longrightarrow> hold fwk_vars \<sigma>o (apply_iv \<iota> \<sigma>c) v = apply_iv \<iota> \<sigma>c v)
      \<and> (\<forall>w\<in>fwk_vars. \<bar>int (hold fwk_vars \<sigma>o (apply_iv \<iota> \<sigma>c) w) - int (apply_iv \<iota> \<sigma>c w)\<bar>
                         \<le> int Dstar))"

theorem composition_W_holds:
  assumes "A1 E \<iota>" shows "composition_W E \<iota>"
proof -
  have out: "var \<iota> \<notin> fwk_vars" by (rule A1_target_outside_fwk[OF assms])
  have pr: "\<forall>w\<in>fwk_vars. p_pert E \<iota> w \<le> delta_A1"
    using A1_pert_per_var[OF assms] by blast
  show ?thesis
    unfolding composition_W_def
    using out pr composition_relaxed_structural[OF out] by blast
qed

text \<open>The effect of do(x') is preserved while holding W (effectiveness is not lost under composition).\<close>

corollary composition_W_keeps_effect:
  assumes "A1 E \<iota>"
  shows "hold fwk_vars \<sigma>o (apply_iv \<iota> \<sigma>c) (var \<iota>) = newval \<iota>"
  by (rule hold_preserves_effectiveness[OF A1_target_outside_fwk[OF assms]])

text \<open>The strict form is recovered: in the limit delta_A1 \<rightarrow> 0 the perturbation probability is 0 (App A "Recovery of strict form").\<close>

theorem composition_strict_recovered:
  assumes "A1 E \<iota>" and "delta_A1 = 0" and "w \<in> fwk_vars"
  shows "p_pert E \<iota> w = 0"
  using A1_pert_per_var[OF assms(1) assms(3)] assms(2) by linarith

text \<open>Union bound over finite K_fwk: total perturbation mass \<le> |K_fwk| * delta_A1.\<close>

theorem composition_W_union_bound:
  assumes "A1 E \<iota>" and "finite fwk_vars"
  shows "(\<Sum>w\<in>fwk_vars. p_pert E \<iota> w) \<le> of_nat (card fwk_vars) * delta_A1"
proof -
  have "(\<Sum>w\<in>fwk_vars. p_pert E \<iota> w) \<le> (\<Sum>w\<in>fwk_vars. delta_A1)"
    by (rule sum_mono) (use A1_pert_per_var[OF assms(1)] in blast)
  also have "\<dots> = of_nat (card fwk_vars) * delta_A1" by simp
  finally show ?thesis .
qed

text \<open>
  The conditional CST theorem with the W-form of composition: the old confounder-bound model
  (composition_relaxed) REMAINS, the W-form is ADDED to it -- the theorem yields both.
\<close>

theorem cst_conditional_W:
  assumes A1h: "A1 E \<iota>" and A2h: "A2 E \<iota>" and A3h: "A3 E \<iota>" and A4h: "A4 E \<iota>"
      and align: "aligned To Tc"
      and adm: "admissible Dstar E \<iota> assum_ok To Tc"
  shows "composition_W E \<iota>
       \<and> effective \<iota>
       \<and> composition_relaxed E \<iota>
       \<and> (\<exists>i w. i < length Tc \<and> i < length To
            \<and> D Dstar To Tc i
            \<and> ac1 To Tc i
            \<and> ac2a To Tc i
            \<and> ac2a_wit w To Tc i
            \<and> ac2b E \<iota>
            \<and> wit_bound w E \<iota> \<le> max (eps_SOE + delta_A1 + alpha)
                                     (delta_A1 + 2 * alpha))"
  using composition_W_holds[OF A1h] cst_conditional[OF A1h A2h A3h A4h align adm] by blast

end  \<comment> \<open>locale cst_composition\<close>

text \<open>
  Consistency + proof of non-vacuity: K_fwk = {0}, A1 = "target is not 0".
  A1 can both be satisfied (var = 7) and violated (var = 0); K_fwk is non-empty.
\<close>

interpretation cst_comp_demo:
  cst_composition
    9077
    "37/10000" "37/10000" "61/10000"
    "\<lambda>E \<iota>. var \<iota> \<noteq> 0" "\<lambda>E \<iota>. True" "\<lambda>E \<iota>. True" "\<lambda>E \<iota>. True"
    "\<lambda>E \<iota>. 0" "\<lambda>E \<iota>. 0" "\<lambda>E \<iota>. 0"
    "\<lambda>E. {}"
    "\<lambda>E \<iota> To Tc i. soe_clause To Tc i"
    "{0}"                                   \<comment> \<open>fwk_vars\<close>
    "\<lambda>E \<iota> w. 0"                           \<comment> \<open>p_pert\<close>
  by unfold_locales (auto simp: D_def)

lemma comp_demo_nonvacuous:
  "cst_comp_demo.composition_W E \<lparr> var = 7, newval = 42, at_event = 0, icls = RegWrite \<rparr>"
  by (rule cst_comp_demo.composition_W_holds) simp

lemma comp_demo_A1_falsifiable:
  "\<not> (\<lambda>E \<iota>. var \<iota> \<noteq> 0) E \<lparr> var = 0, newval = 42, at_event = 0, icls = RegWrite \<rparr>"
  by simp


subsection \<open>8.3 Prop 1, trace-threaded: T_cf^(k) is the baseline of the next step\<close>

context cst_assumptions
begin

text \<open>
  Chain = list of interventions + (n+1) traces: Ts!0 = T_orig, Ts!(k+1) = the T_cf of
  step k; step k+1 takes Ts!(k+1) as its BASELINE (App A induction step). This is the
  REAL chain replacing the boolean-list abstraction in chain_iff_all_atomic.
  The ordering is PART of the claim: for rev \<iota>s the same Ts is not meaningful (a different
  execution, different traces) -- commutativity is not claimed (App A).
\<close>

fun chain_ok :: "envelope \<Rightarrow> intervention list \<Rightarrow> bool \<Rightarrow> trace list \<Rightarrow> bool" where
  "chain_ok E [] ok Ts = (length Ts = 1)"
| "chain_ok E (\<iota> # \<iota>s) ok (To # Tc # Ts) =
     (admissible Dstar E \<iota> ok To Tc \<and> chain_ok E \<iota>s ok (Tc # Ts))"
| "chain_ok E (\<iota> # \<iota>s) ok Ts = False"

text \<open>The REAL statement of Prop 1: chain admissible \<longleftrightarrow> every atomic step, with its OWN baseline, is admissible.\<close>

theorem chain_ok_iff_steps:
  "chain_ok E \<iota>s ok Ts \<longleftrightarrow>
     length Ts = Suc (length \<iota>s)
   \<and> (\<forall>k < length \<iota>s. admissible Dstar E (\<iota>s ! k) ok (Ts ! k) (Ts ! Suc k))"
proof (induct \<iota>s arbitrary: Ts)
  case Nil
  then show ?case by (cases Ts) auto
next
  case (Cons \<iota> \<iota>s)
  note IH = Cons.hyps
  show ?case
  proof (cases Ts)
    case Nil then show ?thesis by simp
  next
    case (Cons To Ts')
    show ?thesis
    proof (cases Ts')
      case Nil with \<open>Ts = To # Ts'\<close> show ?thesis by simp
    next
      case (Cons Tc Ts'')
      have "chain_ok E (\<iota> # \<iota>s) ok (To # Tc # Ts'')
            \<longleftrightarrow> admissible Dstar E \<iota> ok To Tc \<and> chain_ok E \<iota>s ok (Tc # Ts'')" by simp
      also have "\<dots> \<longleftrightarrow> admissible Dstar E \<iota> ok To Tc
                     \<and> length (Tc # Ts'') = Suc (length \<iota>s)
                     \<and> (\<forall>k < length \<iota>s. admissible Dstar E (\<iota>s ! k) ok
                            ((Tc # Ts'') ! k) ((Tc # Ts'') ! Suc k))"
        using IH by simp
      also have "\<dots> \<longleftrightarrow> length (To # Tc # Ts'') = Suc (length (\<iota> # \<iota>s))
                     \<and> (\<forall>k < length (\<iota> # \<iota>s). admissible Dstar E ((\<iota> # \<iota>s) ! k) ok
                            ((To # Tc # Ts'') ! k) ((To # Tc # Ts'') ! Suc k))"
        by (auto simp: less_Suc_eq_0_disj)
      finally show ?thesis using \<open>Ts = To # Ts'\<close> \<open>Ts' = Tc # Ts''\<close> by simp
    qed
  qed
qed

text \<open>
  App A induction step, verbatim: extending the chain by one step = adding an atomic step
  that takes the LAST T_cf as baseline. "Applying Theorem 1 to the atomic step with T_cf^(n) as the
  original trace yields admissibility for the extended chain."
\<close>

theorem chain_extend:
  assumes "chain_ok E \<iota>s ok Ts"
  shows "chain_ok E (\<iota>s @ [\<iota>]) ok (Ts @ [T]) \<longleftrightarrow> admissible Dstar E \<iota> ok (last Ts) T"
proof -
  let ?S = "\<lambda>k. admissible Dstar E ((\<iota>s @ [\<iota>]) ! k) ok ((Ts @ [T]) ! k) ((Ts @ [T]) ! Suc k)"
  from assms have len: "length Ts = Suc (length \<iota>s)"
    and steps: "\<forall>k < length \<iota>s. admissible Dstar E (\<iota>s ! k) ok (Ts ! k) (Ts ! Suc k)"
    by (simp_all add: chain_ok_iff_steps)
  have ne: "Ts \<noteq> []" using len by auto
  have lastTs: "last Ts = Ts ! length \<iota>s"
    using last_conv_nth[OF ne] len by simp
  have old: "\<And>k. k < length \<iota>s \<Longrightarrow>
      ?S k = admissible Dstar E (\<iota>s ! k) ok (Ts ! k) (Ts ! Suc k)"
    using len by (simp add: nth_append)
  have new: "?S (length \<iota>s) = admissible Dstar E \<iota> ok (last Ts) T"
    using len lastTs by (simp add: nth_append)
  have split: "(\<forall>k < Suc (length \<iota>s). ?S k) \<longleftrightarrow> admissible Dstar E \<iota> ok (last Ts) T"
  proof
    assume a1: "\<forall>k < Suc (length \<iota>s). ?S k"
    have "?S (length \<iota>s)" using a1[rule_format, of "length \<iota>s"] by simp
    then show "admissible Dstar E \<iota> ok (last Ts) T" by (rule new[THEN iffD1])
  next
    assume a: "admissible Dstar E \<iota> ok (last Ts) T"
    show "\<forall>k < Suc (length \<iota>s). ?S k"
    proof (intro allI impI)
      fix k assume "k < Suc (length \<iota>s)"
      then consider "k < length \<iota>s" | "k = length \<iota>s" by (auto simp: less_Suc_eq)
      then show "?S k"
      proof cases
        case 1
        have "admissible Dstar E (\<iota>s ! k) ok (Ts ! k) (Ts ! Suc k)" using steps 1 by blast
        then show ?thesis by (rule old[OF 1, THEN iffD2])
      next
        case 2
        have "?S (length \<iota>s)" by (rule new[THEN iffD2, OF a])
        with 2 show ?thesis by simp
      qed
    qed
  qed
  have lens: "length (Ts @ [T]) = Suc (length (\<iota>s @ [\<iota>]))" using len by simp
  have goal_eq: "chain_ok E (\<iota>s @ [\<iota>]) ok (Ts @ [T]) \<longleftrightarrow>
       (length (Ts @ [T]) = Suc (length (\<iota>s @ [\<iota>])) \<and> (\<forall>k < Suc (length \<iota>s). ?S k))"
    unfolding chain_ok_iff_steps by simp
  show ?thesis unfolding goal_eq using lens split by blast
qed

text \<open>The conditional CST result for EVERY step of the chain (Theorem 1 step by step, each on its own baseline).\<close>

theorem chain_conditional:
  assumes hyps: "\<And>\<iota>. \<iota> \<in> set \<iota>s \<Longrightarrow> A1 E \<iota> \<and> A2 E \<iota> \<and> A3 E \<iota> \<and> A4 E \<iota>"
      and align: "\<And>k. k < length \<iota>s \<Longrightarrow> aligned (Ts ! k) (Ts ! Suc k)"
      and chain: "chain_ok E \<iota>s ok Ts"
      and k: "k < length \<iota>s"
  shows "effective (\<iota>s ! k)
       \<and> composition_relaxed E (\<iota>s ! k)
       \<and> (\<exists>i w. i < length (Ts ! Suc k) \<and> i < length (Ts ! k)
            \<and> D Dstar (Ts ! k) (Ts ! Suc k) i
            \<and> ac1 (Ts ! k) (Ts ! Suc k) i
            \<and> ac2a (Ts ! k) (Ts ! Suc k) i
            \<and> ac2a_wit w (Ts ! k) (Ts ! Suc k) i
            \<and> ac2b E (\<iota>s ! k)
            \<and> wit_bound w E (\<iota>s ! k) \<le> max (eps_SOE + delta_A1 + alpha)
                                          (delta_A1 + 2 * alpha))"
proof -
  from chain k have adm: "admissible Dstar E (\<iota>s ! k) ok (Ts ! k) (Ts ! Suc k)"
    by (simp add: chain_ok_iff_steps)
  from hyps[OF nth_mem[OF k]]
  have A: "A1 E (\<iota>s ! k)" "A2 E (\<iota>s ! k)" "A3 E (\<iota>s ! k)" "A4 E (\<iota>s ! k)" by auto
  show ?thesis by (rule cst_conditional[OF A align[OF k] adm])
qed

text \<open>
  A1^(n+1) \<le> A1^(n) + delta_A1 (App A): when the chain grows by one step the accumulated A1 envelope
  increases by exactly delta_A1; total n * delta_A1 (accum_delta_eq).
\<close>

lemma chain_delta_step:
  "accum_delta (length (\<iota>s @ [\<iota>])) = accum_delta (length \<iota>s) + delta_A1"
  by simp

text \<open>
  Witness envelopes of the chain: even though the steps are DEPENDENT, the union bound holds (independence
  is not assumed -- App A "tighter bounds under independence are not asserted").
  Total \<le> witness-aware sweep_ub \<le> n * blanket.
\<close>

definition chain_actual :: "envelope \<Rightarrow> intervention list \<Rightarrow> ac2a_witness list \<Rightarrow> real" where
  "chain_actual E \<iota>s ws = sum_list (map2 (\<lambda>\<iota> w. wit_bound w E \<iota>) \<iota>s ws)"

theorem chain_envelope_bound:
  assumes hyps: "\<And>\<iota>. \<iota> \<in> set \<iota>s \<Longrightarrow> A1 E \<iota> \<and> A3 E \<iota> \<and> A4 E \<iota>"
      and len: "length ws = length \<iota>s"
  shows "chain_actual E \<iota>s ws \<le> sweep_ub ws
       \<and> sweep_ub ws \<le> of_nat (length \<iota>s) * blanket"
proof -
  have "chain_actual E \<iota>s ws \<le> sweep_ub ws"
    using len[symmetric] hyps unfolding chain_actual_def sweep_ub_def
  proof (induct \<iota>s ws rule: list_induct2)
    case Nil show ?case by simp
  next
    case (Cons \<iota> \<iota>s w ws)
    have h: "A1 E \<iota>" "A3 E \<iota>" "A4 E \<iota>" using Cons.prems by auto
    have ih: "sum_list (map2 (\<lambda>\<iota> w. wit_bound w E \<iota>) \<iota>s ws) \<le> sum_list (map wit_ub ws)"
      by (rule Cons.hyps) (use Cons.prems in auto)
    have "wit_bound w E \<iota> \<le> wit_ub w" by (rule wit_bound_le_ub[OF h])
    with ih show ?case by simp
  qed
  moreover have "sweep_ub ws \<le> of_nat (length \<iota>s) * blanket"
    using sweep_ub_tighter[of ws] len by simp
  ultimately show ?thesis by blast
qed

end  \<comment> \<open>context cst_assumptions\<close>

text \<open>
  Concrete 2-step chain (within-boot regime): T0 = ex_orig, T1 changes rax,
  T2 changes T1's rax once more; the baseline of the second step is T1.
\<close>

definition ch_T1 :: trace where
  "ch_T1 = [ ev 10 1 0 5 1000, ev 14 2 0 6 1050 ]"

definition ch_T2 :: trace where
  "ch_T2 = [ ev 10 1 0 5 1000, ev 14 2 0 7 1050 ]"

definition ch_E :: envelope where
  "ch_E = \<lparr> instr = 1, wl_class = 1, gw_type = 1, scp = PerEvent, s_in = {7}, s_out = {} \<rparr>"

definition ch_iv1 :: intervention where
  "ch_iv1 = \<lparr> var = 7, newval = 42, at_event = 1, icls = RegWrite \<rparr>"

definition ch_iv2 :: intervention where
  "ch_iv2 = \<lparr> var = 7, newval = 43, at_event = 1, icls = RegWrite \<rparr>"

lemma chain_demo_step1: "admissible 9077 ch_E ch_iv1 True ex_orig ch_T1"
  unfolding admissible_def cst_v1_covered_def ch_E_def ch_iv1_def
  by (simp, eval)

lemma chain_demo_step2: "admissible 9077 ch_E ch_iv2 True ch_T1 ch_T2"
  unfolding admissible_def cst_v1_covered_def ch_E_def ch_iv2_def
  by (simp, eval)

lemma chain_demo:
  "cst_withinboot.chain_ok ch_E [ch_iv1, ch_iv2] True [ex_orig, ch_T1, ch_T2]"
  by (simp add: cst_withinboot.chain_ok.simps chain_demo_step1 chain_demo_step2)

text \<open>The baseline shift made concrete: the second step is measured against T1, not T_orig.\<close>

lemma chain_demo_baseline_shift:
  "cst_withinboot.chain_ok ch_E [ch_iv1, ch_iv2] True [ex_orig, ch_T1, ch_T2]
   \<longleftrightarrow> admissible 9077 ch_E ch_iv1 True ex_orig ch_T1 \<and> admissible 9077 ch_E ch_iv2 True ch_T1 ch_T2"
  by (simp add: cst_withinboot.chain_ok.simps)

end
