(*
  CST_Model.thy  --  EXTp / Counterfactual Soundness Theorem
  =========================================================
  FAZ 0: Saf EXTp modeli (executable defs) + FAZ 1 locale iskeleti.

  Bu dosya, App A'daki yari-formal ispati makine-kontrollu KOSULLU
  teoreme yukseltmenin taban katmanidir. seL4 harness'ina VE lifting
  acigina KASITLI olarak dokunmaz -- cunku kosullu teorem (A1-A4
  hipotez olarak alindiginda) lifting'den bagimsizdir. Lifting yalnizca
  Faz 3'te, A1'i K_verified icin discharge etmek istersek devreye girer.

  Kaynak eslesmesi:
    - datatype/record'lar  : extp.tex sec:framework, sec:soe, App A "Notation"
    - D (divergence)       : extp_formal_properties.md P2/P3, App A
    - envelope E           : extp.tex sec:cst, CST doc sec:3.4
    - dort-adimli check    : extp.tex sec:intervention (1)-(4)
    - locale A1-A4         : extp.tex Table tab:assumptions, CST doc sec:3.2 / sec:5.4

  Durum notlari (FAZ 0 + FAZ 1 + FAZ 2 tamam, sorry YOK):
    - Bu katmandaki TUM tanimlar total ve executable (by eval ile dogrulandi).
    - Kosullu teorem cst_conditional (Teorem 1, => yonu) ISPATLI; uc bounding
      lemma (App A), HP witness insasi (AC2(b)), Proposition 1 (sirali
      kompozisyon) ve locale tutarlilik yorumlamasi ISPATLI.
    - Olasilik sinirlari (delta_A1, eps_SOE, alpha) SOYUT reel parametre olarak
      girer; Clopper-Pearson Isabelle'de ISPATLANMAZ (olcumdur) -- sadece
      union-bound aritmetigi ispatlanir.
    - Geriye kalan tek acik = FAZ 3 (lifting), §7'de bilincli stub.
    - 2026-09-01 (§8): statement-fidelity denetiminin iki "prose" kosesi kapatildi:
      composition W/K_fwk formunda (hold, pert_bounded, locale cst_composition,
      cst_conditional_W) + Prop 1 trace-zincirli (chain_ok, chain_extend,
      chain_conditional). Toplam 115 fact, sorry YOK.
*)

theory CST_Model
  imports Complex_Main "HOL-Library.Word"
begin

section \<open>1. Gozlemlenebilir yuzey ve trace (SOE 4-tuple + timing)\<close>

text \<open>
  4-tuple gozlemlenebilir yuzey (extp.tex sec:soe): rip, exit_reason,
  exit_qual, rax. Faz 0'da nat kullaniyoruz; ileride 64 word'e cevrilebilir.
\<close>

text \<open>
  (e) GERCEK register genislikleri: VT-x/VMCS alanlari makine-word'udur.
  rip / exit_qual / rax = 64-bit; exit_reason = 32-bit VMCS alani. Gozlemlenebilir
  yuzey yalnizca ESITLIKLE karsilastirilir (soe_clause), dolayisiyla word'e cevirmek
  TASMA RISKI TASIMAZ. timing = nat KALIR (TSC aritmetigi; wraparound bilincli
  olarak kapsam disi -- fresh-boot disiplini kisa izler + oturum-ici reset saglar).
\<close>

record observable =
  rip         :: "64 word"
  exit_reason :: "32 word"
  exit_qual   :: "64 word"
  rax         :: "64 word"

text \<open>Bir VM-exit olayi: gozlemlenebilir 4-tuple + per-event timing \<open>\<Delta>\<^sub>i\<close> (cycle).\<close>

record event =
  obs    :: observable
  timing :: nat

type_synonym trace = "event list"

definition aligned :: "trace \<Rightarrow> trace \<Rightarrow> bool" where
  "aligned To Tc \<longleftrightarrow> length To = length Tc"


section \<open>2. Divergence detection fonksiyonu D\<close>

text \<open>
  D'nin iki clause'u (App A, extp_formal_properties.md):
    - SOE clause  : 4-tuple farki (deterministik, FPR = 0 under A4)
    - timing clause: |Delta_cf - Delta_orig| > Dstar (olasiliksal, FPR <= alpha)
\<close>

definition soe_clause :: "trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool" where
  "soe_clause To Tc i \<longleftrightarrow> obs (To ! i) \<noteq> obs (Tc ! i)"

definition timing_clause :: "nat \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool" where
  "timing_clause Dstar To Tc i \<longleftrightarrow>
     \<bar>int (timing (Tc ! i)) - int (timing (To ! i))\<bar> > int Dstar"

definition D :: "nat \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool" where
  "D Dstar To Tc i \<longleftrightarrow> soe_clause To Tc i \<or> timing_clause Dstar To Tc i"

text \<open>Iz uzerinde herhangi bir olayda divergence var mi?\<close>

definition diverges :: "nat \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  "diverges Dstar To Tc \<longleftrightarrow> (\<exists>i < length Tc. D Dstar To Tc i)"


subsection \<open>2.1 AC2(a) taniklarinin ayrismasi ve BAGIMSIZLIGI\<close>

text \<open>
  App A item (iv): "The structural-clause version (4-tuple delta) and timing-clause
  version each INDEPENDENTLY witness AC2(a)." Bu ifadeyi modele tasiyoruz:
  D'nin iki clause'u iki AYRI tanik tipi; D = (en az bir tanik ateslenir).

  "Independently" ifadesi matematiksel olarak SU DEMEK: hicbiri digerini
  gerektirmez. Bunu somut karsi-orneklerle ISPATLIYORUZ (asagida
  witness_indep_*), yani bagimsizlik iddiasi prose'da kalmiyor.
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

text \<open>D, tanik varliginin tam karsiligidir (OR-clause yapisinin ayrismasi).\<close>

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

text \<open>Her tanik TEK BASINA yeterlidir (each independently witnesses).\<close>

lemma structural_witness_suffices:
  "soe_clause To Tc i \<Longrightarrow> D Dstar To Tc i"
  by (simp add: D_def)

lemma timing_witness_suffices:
  "timing_clause Dstar To Tc i \<Longrightarrow> D Dstar To Tc i"
  by (simp add: D_def)

text \<open>
  Bir sweep, input basina bir SONUC verir: ya admissible claim (bir tanikla,
  Some w) ya da D=false (sessiz, None). `emitted_of`, yalnizca admissible
  claim'lerin tanik listesini cikarir -- sessiz input'lar DUSER.
\<close>

definition emitted_of :: "ac2a_witness option list \<Rightarrow> ac2a_witness list" where
  "emitted_of xs = map the (filter (\<lambda>x. x \<noteq> None) xs)"

lemma emitted_of_Nil [simp]: "emitted_of [] = []"
  by (simp add: emitted_of_def)

lemma emitted_of_None [simp]: "emitted_of (None # xs) = emitted_of xs"
  by (simp add: emitted_of_def)

lemma emitted_of_Some [simp]: "emitted_of (Some w # xs) = w # emitted_of xs"
  by (simp add: emitted_of_def)


subsection \<open>2.2 aligned: indeks guvenligi ve A4'un operasyonel ifadesi\<close>

lemma aligned_index_safe:
  "aligned To Tc \<Longrightarrow> i < length Tc \<Longrightarrow> i < length To"
  by (simp add: aligned_def)

text \<open>
  A4'un operasyonel ifadesi (extp.tex sec:soe): mudahale yokken hizalanmis
  izlerde 4-tuple noktasal olarak esittir. `aligned` burada gercekten is yapar:
  her iki izde de i-inci olay MEVCUTTUR.
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


section \<open>3. Intervention modeli ve validity envelope E\<close>

datatype scope = PerEvent | PerWindow | Global

datatype iclass = NopCount | RegWrite | InputValue | CachePreload

text \<open>
  do(X = x') at event i. X ve x' Faz 0'da nat ID/deger; icls = mudahale sinifi.
  (CST doc sec:2.2 intervention surface.)
\<close>

record intervention =
  var      :: nat      \<comment> \<open>hedef degisken X'in ID'si\<close>
  newval   :: nat      \<comment> \<open>x'\<close>
  at_event :: nat      \<comment> \<open>e_i indeksi\<close>
  icls     :: iclass

text \<open>
  Validity envelope E (extp.tex sec:cst, CST doc sec:3.4): in-scope /
  out-of-scope sentinel'lariyla bir record. s_in = valide mudahale yuzeyi
  (S_in), s_out = disaridaki sessiz kanallar (S_out).
\<close>

record envelope =
  instr    :: nat          \<comment> \<open>timing enstruman ID'si (S1 / S2)\<close>
  wl_class :: nat          \<comment> \<open>workload sinifi\<close>
  gw_type  :: nat          \<comment> \<open>guest-workload tipi\<close>
  scp      :: scope
  s_in     :: "nat set"
  s_out    :: "nat set"

text \<open>
  CST v1.0 kapsam predikati (extp.tex sec:intervention adim 1):
  yalnizca per-event scope ve dort valide mudahale sinifi.
\<close>

definition cst_v1_covered :: "envelope \<Rightarrow> intervention \<Rightarrow> bool" where
  "cst_v1_covered E \<iota> \<longleftrightarrow>
     scp E = PerEvent \<and>
     icls \<iota> \<in> {NopCount, RegWrite, InputValue, CachePreload} \<and>
     s_in E \<inter> s_out E = {}"          \<comment> \<open>S_in ve S_out disjoint (wf kosulu)\<close>


subsection \<open>3.1 do-operatorunun anlambilimi (Pearl severance)\<close>

text \<open>
  Pearl's do(X=x') "X'i x'e zorlar, X'e giden tum nedensel baglantilari keser"
  (extp.tex sec:background; App A item i "effectiveness"). Guest durumunu
  degisken-degeri valuation'i olarak modelliyoruz; apply_iv, X'i x'e set eden
  fonksiyonel guncelleme. Effectiveness = mudahale sonrasi X'in x' okunmasi;
  severance = sonucun X'in ONCEKI degerinden BAGIMSIZ olmasi + diger
  degiskenlere DOKUNMAMASI (modularity/composition ile baglantili).
\<close>

type_synonym valuation = "nat \<Rightarrow> nat"

definition apply_iv :: "intervention \<Rightarrow> valuation \<Rightarrow> valuation" where
  "apply_iv \<iota> \<sigma> = \<sigma>(var \<iota> := newval \<iota>)"

definition effective :: "intervention \<Rightarrow> bool" where
  "effective \<iota> \<longleftrightarrow> (\<forall>\<sigma>. apply_iv \<iota> \<sigma> (var \<iota>) = newval \<iota>)"

text \<open>Effectiveness: do() X'i basariyla x'e set eder.\<close>
lemma apply_iv_severs: "apply_iv \<iota> \<sigma> (var \<iota>) = newval \<iota>"
  by (simp add: apply_iv_def)

text \<open>Locality: X disindaki degiskenler degismez (do() yalnizca X'e giren oklari keser).\<close>
lemma apply_iv_local: "y \<noteq> var \<iota> \<Longrightarrow> apply_iv \<iota> \<sigma> y = \<sigma> y"
  by (simp add: apply_iv_def)

text \<open>Severance: X'in mudahale-sonrasi degeri, ONCEKI degerinden bagimsiz.\<close>
lemma apply_iv_indep_pre: "apply_iv \<iota> \<sigma> (var \<iota>) = apply_iv \<iota> \<sigma>' (var \<iota>)"
  by (simp add: apply_iv_def)

text \<open>Effectiveness insaat geregi her mudahale icin gecerli.\<close>
lemma effective_holds: "effective \<iota>"
  by (simp add: effective_def apply_iv_severs)

text \<open>Somut ornek: reg_7 := 42; hedef zorlanir, komsu degisken (3) korunur.\<close>
lemma sanity_effective_forces:
  "apply_iv \<lparr> var = 7, newval = 42, at_event = 0, icls = RegWrite \<rparr> (\<lambda>_. 0) 7 = 42"
  by eval

lemma sanity_effective_local:
  "apply_iv \<lparr> var = 7, newval = 42, at_event = 0, icls = RegWrite \<rparr> (\<lambda>_. 5) 3 = 5"
  by eval


section \<open>4. Dort-adimli admissibility check\<close>

text \<open>
  extp.tex sec:intervention: claim yayinlanmadan once dort adim.
    (1) E'nin bilesenleri CST v1.0 kapsamiyla eslesir
    (2) A1-A4 assumption referanslari mevcut ve guncel   (assum_ok flag)
    (3) D = true bir olayda gercekten gozlemlendi
    (4) X valide mudahale yuzeyinde (var in S_in)
  Herhangi biri false -> claim yok (structured invalidity tag).
\<close>

definition admissible ::
    "nat \<Rightarrow> envelope \<Rightarrow> intervention \<Rightarrow> bool \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  "admissible Dstar E \<iota> assum_ok To Tc \<longleftrightarrow>
     cst_v1_covered E \<iota>           \<comment> \<open>adim 1\<close>
   \<and> assum_ok                        \<comment> \<open>adim 2\<close>
   \<and> diverges Dstar To Tc           \<comment> \<open>adim 3\<close>
   \<and> var \<iota> \<in> s_in E"                \<comment> \<open>adim 4\<close>

text \<open>
  Claim emission = admissible (extp.tex: check gecerse EXTp claim yayinlar,
  aksi halde invalidity tag). Boylece Teorem 1'in (<=) yonu -- "check gecti
  => claim yayinlandi" -- INSAAT GEREGI (definitional) dogru.
\<close>

definition emits ::
    "nat \<Rightarrow> envelope \<Rightarrow> intervention \<Rightarrow> bool \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> bool" where
  "emits Dstar E \<iota> assum_ok To Tc \<longleftrightarrow> admissible Dstar E \<iota> assum_ok To Tc"

lemma left_direction:  \<comment> \<open>Teorem 1, (<=) yonu -- FAZ 1, insaat geregi\<close>
  "emits Dstar E \<iota> assum_ok To Tc \<longleftrightarrow> admissible Dstar E \<iota> assum_ok To Tc"
  by (simp add: emits_def)


section \<open>5. Sanity checks (executable)\<close>

definition ev :: "64 word \<Rightarrow> 32 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow> event" where
  "ev r er eq a t =
     \<lparr> obs = \<lparr> rip = r, exit_reason = er, exit_qual = eq, rax = a \<rparr>, timing = t \<rparr>"

definition ex_orig :: trace where
  "ex_orig = [ ev 10 1 0 5 1000, ev 14 2 0 5 1050 ]"

text \<open>
  Sanity check'ler ISPATLANMIS gercekler olarak (by eval) -- modelin dogru
  hesapladigini makine dogrular, yalnizca "typecheck ediyor" degil.
\<close>

text \<open>Ayni iz, intervention yok -> divergence yok.\<close>
lemma sanity_no_divergence: "\<not> diverges 500 ex_orig ex_orig"
  by eval

text \<open>rax @1 degisti (SOE clause) -> divergence var.\<close>
lemma sanity_soe_clause:
  "diverges 500 ex_orig [ ev 10 1 0 5 1000, ev 14 2 0 9 1050 ]"
  by eval

text \<open>timing @0 +2000 cycle sicradi, Dstar=500 (timing clause) -> True.\<close>
lemma sanity_timing_clause:
  "diverges 500 ex_orig [ ev 10 1 0 5 3000, ev 14 2 0 5 1050 ]"
  by eval

text \<open>timing @0 +400 cycle, Dstar=500 (esik altinda) -> divergence yok.\<close>
lemma sanity_below_threshold:
  "\<not> diverges 500 ex_orig [ ev 10 1 0 5 1400, ev 14 2 0 5 1050 ]"
  by eval


subsection \<open>5.1 Tanik BAGIMSIZLIGI -- somut karsi-orneklerle ispat\<close>

text \<open>
  "Each INDEPENDENTLY witnesses AC2(a)" iddiasinin matematiksel icerigi:
  hicbir clause digerini GEREKTIRMEZ. Iki karsi-ornek bunu kesin olarak kurar.
\<close>

definition ex_soe_only :: trace where    \<comment> \<open>rax @1 farkli, timing AYNI\<close>
  "ex_soe_only = [ ev 10 1 0 5 1000, ev 14 2 0 9 1050 ]"

definition ex_tim_only :: trace where    \<comment> \<open>timing @0 farkli, 4-tuple AYNI\<close>
  "ex_tim_only = [ ev 10 1 0 5 3000, ev 14 2 0 5 1050 ]"

text \<open>(1) Yapisal tanik ateslenir, zamanlama tanigi ATESLENMEZ.\<close>
lemma witness_indep_structural:
  "witnesses StructuralW 500 ex_orig ex_soe_only 1
   \<and> \<not> witnesses TimingW 500 ex_orig ex_soe_only 1"
  by eval

text \<open>(2) Zamanlama tanigi ateslenir, yapisal tanik ATESLENMEZ.\<close>
lemma witness_indep_timing:
  "witnesses TimingW 500 ex_orig ex_tim_only 0
   \<and> \<not> witnesses StructuralW 500 ex_orig ex_tim_only 0"
  by eval

text \<open>
  Sonuc: iki tanik mantiksal olarak BAGIMSIZ -- ne biri digerini gerektirir,
  ne de ortak bir clause'a indirgenebilirler. Dolayisiyla D'nin OR yapisi
  gercekten iki AYRI kanidir, tek kanitin iki yazilisi degil.
\<close>

subsection \<open>5.2 A2 TAUTOLOJI DEGIL -- yanlislanabilirligin somut kaniti\<close>

text \<open>
  Reviewer itirazi: "A2, D'nin tanimini tekrar etmiyor mu? Yani tautoloji mi?"
  CEVAP: Hayir. A2 gercek, YANLISLANABILIR bir iddiadir -- cunku GERCEK bir
  durum farkinin D'ye HIC yansimadigi durumlar VARDIR. Asagida somut bir tane:
  timing @0'da 400 cycle fark var (gercek bir pertürbasyon), ama Dstar=500
  esiginin ALTINDA oldugu icin D ateslenmiyor.

  Eger boyle bir fark S_in ICINDE bir nedensel etki olsaydi, A2 IHLAL edilirdi.
  Demek ki A2 bos bir ifade degil: dunyaya dair bir sey soyluyor ve yanlis
  cikabilir. (Bu, App A'nin "silent leak" / sub-Dstar sinif tartismasinin
  makine-kontrollu karsiligidir.)
\<close>

definition ex_silent :: trace where   \<comment> \<open>timing @0 +400: GERCEK fark, D'ye yansimaz\<close>
  "ex_silent = [ ev 10 1 0 5 1400, ev 14 2 0 5 1050 ]"

lemma silent_effect_exists:
  "timing (ex_silent ! 0) \<noteq> timing (ex_orig ! 0)
   \<and> \<not> diverges 500 ex_orig ex_silent"
  by eval

text \<open>
  Ayrica: bu fark 4-tuple yuzeyinde de gorunmez -- yani her iki clause da sessiz.
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


section \<open>6. CST assumption locale (A1-A4) -- FAZ 2: kosullu teorem\<close>

text \<open>
  A1-A4 (extp.tex Table tab:assumptions) SOYUT predicate; olasilik sinirlari
  SOYUT reel parametre. p_soe / p_tim / p_conf = App A'nin uc bounding
  argumanindaki OLCULEN (bilinmeyen) katki miktarlari; A1/A3/A4 assumption'lari
  onlari eps_SOE / alpha / (delta_A1+alpha) ile SINIRLAR. Isabelle bu reel
  sayilari uretmez -- Clopper-Pearson / MI kalibrasyonundan disaridan girer;
  teorem yalnizca union-bound aritmetigi + mantiksal kompozisyon ustunde calisir.

  eff_vars E = olayda "etkiyi olusturan" gozlemlenebilir yuzey degiskenleri
  (HP witness insasinda W = S_in \ eff_vars).
\<close>

locale cst_assumptions =
  fixes Dstar    :: nat
    and delta_A1 :: real        \<comment> \<open>CapSep ampirik zarfi (A1)\<close>
    and eps_SOE  :: real        \<comment> \<open>SOE Clopper-Pearson ust siniri (A4)\<close>
    and alpha    :: real        \<comment> \<open>MI realized FPR (A3)\<close>
    and A1 :: "envelope \<Rightarrow> intervention \<Rightarrow> bool"   \<comment> \<open>modularity\<close>
    and A2 :: "envelope \<Rightarrow> intervention \<Rightarrow> bool"   \<comment> \<open>observational completeness / S_in\<close>
    and A3 :: "envelope \<Rightarrow> intervention \<Rightarrow> bool"   \<comment> \<open>confounder bound < Dstar\<close>
    and A4 :: "envelope \<Rightarrow> intervention \<Rightarrow> bool"   \<comment> \<open>replay determinism (SOE)\<close>
    and p_soe  :: "envelope \<Rightarrow> intervention \<Rightarrow> real"  \<comment> \<open>SOE-clause coincidence katkisi\<close>
    and p_tim  :: "envelope \<Rightarrow> intervention \<Rightarrow> real"  \<comment> \<open>timing-clause coincidence katkisi\<close>
    and p_conf :: "envelope \<Rightarrow> intervention \<Rightarrow> real"  \<comment> \<open>confounder katkisi (modulo A1)\<close>
    and eff_vars :: "envelope \<Rightarrow> nat set"           \<comment> \<open>etkiyi olusturan yuzey degiskenleri\<close>
    and effect_at :: "envelope \<Rightarrow> intervention \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool"
        \<comment> \<open>YER ALTINDAKI nedensel etki -- D DEGIL; bagimsiz belirtilmis\<close>
  assumes prob_nonneg: "0 \<le> delta_A1" "0 \<le> eps_SOE" "0 \<le> alpha"
      and prob_le_one:  "delta_A1 \<le> 1" "eps_SOE \<le> 1" "alpha \<le> 1"
      and A4_bounds_soe:  "\<And>E \<iota>. A4 E \<iota> \<Longrightarrow> 0 \<le> p_soe E \<iota> \<and> p_soe E \<iota> \<le> eps_SOE"
      and A3_bounds_tim:  "\<And>E \<iota>. A3 E \<iota> \<Longrightarrow> 0 \<le> p_tim E \<iota> \<and> p_tim E \<iota> \<le> alpha"
      and A1_bounds_conf: "\<And>E \<iota>. A1 E \<iota> \<Longrightarrow> 0 \<le> p_conf E \<iota> \<and> p_conf E \<iota> \<le> delta_A1 + alpha"
      and eff_subset:     "\<And>E. eff_vars E \<subseteq> s_in E"
      \<comment> \<open>A2'nin OPERASYONEL icerigi: S_in ICINDEKI her nedensel etki D'ye yansir.
          Dikkat: `var \<iota> \<in> s_in E` GUARD'i sart -- A2, S_out hakkinda HICBIR
          sey soylemez (App A: "explicitly out of A2's scope").\<close>
      and A2_manifests:
        "\<And>E \<iota> To Tc i. A2 E \<iota> \<Longrightarrow> var \<iota> \<in> s_in E
                        \<Longrightarrow> effect_at E \<iota> To Tc i \<Longrightarrow> D Dstar To Tc i"
begin

text \<open>
  App A'nin claim basina rapor ettigi kalinti epistemik zarf:
  residual = eps_SOE + delta_A1 + alpha (union bound). AC2(b) W2 kosulunun siniri.
\<close>

definition residual :: real where
  "residual = eps_SOE + delta_A1 + alpha"

lemma residual_nonneg: "0 \<le> residual"
  using prob_nonneg by (simp add: residual_def)

lemma residual_le_three: "residual \<le> 3"
  using prob_le_one by (simp add: residual_def)


subsection \<open>6.1 Bounding lemmalari (App A) -- ispatli\<close>

text \<open>
  App A'daki uc "bounding" argumani. Her biri, ilgili assumption'in katki
  miktarina koydugu ust siniri disari verir; ispat, locale assumption'larindan
  dogrudan cikar.
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
  App A'nin "Remark on lemma content" uyarisi: lemmanin icerigi "A2 kendi
  kapsamini ima eder" (bu DEFINITIONAL olurdu) DEGIL; iki BAGIMSIZ belirtilmis
  bilesenin -- A2 (neyin gozlemlenebilir oldugu) ve emission policy (hangi
  gozlem altinda claim yayinlandigi) -- TUTARLILIGIDIR.

  Modelde bu bagimsizlik YAPISALDIR:
    - `emits` / `admissible` TOP-LEVEL tanimlar; A2'ye HIC referans vermezler.
    - `A2` + `effect_at` locale PARAMETRELERIDIR; emission'a referans vermezler.
  Asagidaki iki lemma bu iki bagimsiz bileseni birbirine baglar.
\<close>

text \<open>
  (i) SOUNDNESS yonu: gozlemlenebilir divergence OLMADAN claim yayinlanmaz.
  Emission policy'nin kendi yapisindan gelir (A2 gerekmez).
\<close>

lemma emits_implies_divergence:
  "emits Dstar E \<iota> assum_ok To Tc \<Longrightarrow> diverges Dstar To Tc"
  by (simp add: emits_def admissible_def)

text \<open>
  (ii) SCOPE-COMPLETENESS yonu: S_in ICINDEKI hicbir nedensel etki
  RAPORSUZ kalmaz. A2 burada GERCEKTEN is yapar -- kaldirilirsa lemma cokerdi.
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
  (iii) Tam bicim: envelope adimlari gecerken S_in-ici bir etki VARSA,
  claim MUTLAKA yayinlanir. "No in-scope effect goes unreported."
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
  (iv) S_out KAPSAM DISI: A2'nin guard'i `var \<iota> \<in> s_in E`. Guard saglanmazsa
  A2_manifests HICBIR sey vermez -- yani CST, S_out uzerinden gerceklesen
  etkiler icin sessiz kalir ve bu bir SOUNDNESS iddiasi degil, KAPSAM ifadesidir.
  Asagida, claim yayinlanmadigi durumda gozlemlenebilir divergence de
  olmadigini gosteriyoruz (scope-honest silence).
\<close>

lemma scope_honest_silence:
  "\<not> diverges Dstar To Tc \<Longrightarrow> \<not> emits Dstar E \<iota> assum_ok To Tc"
  using emits_implies_divergence by blast


subsection \<open>6.16 Silent-leak sinifi = scope siniri (adim i)\<close>

text \<open>
  MI'in sub-Delta* silent-leak sinifi (extp.tex sec:mi; sec:cst Threat 2): do(x')
  gozlemlenebilir yuzeyde HICBIR clause atesletmeyen bir etki uretebilir. Paper
  bunlari "explicitly deferred to a future CMD property class" diyor. Burada bu
  ifadeyi PROSE'dan KANITLANMIS BIR SCOPE-SINIRINA ceviriyoruz:

    A2 altinda, S_in ICINDE sessiz sizinti IMKANSIZDIR; dolayisiyla her sessiz
    sizinti ZORUNLU olarak S_out'tadir (var iota ∉ s_in E). Yani CST'nin scope
    siniri sadece ilan edilmiyor, assumption yapisi tarafindan ZORLANIYOR.

  Sessiz sizinti = etki var, ama D'nin HER IKI clause'u da sessiz.
\<close>

definition silent_leak :: "trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool" where
  "silent_leak To Tc i \<longleftrightarrow> \<not> soe_clause To Tc i \<and> \<not> timing_clause Dstar To Tc i"

lemma silent_leak_iff_not_D: "silent_leak To Tc i \<longleftrightarrow> \<not> D Dstar To Tc i"
  by (auto simp: silent_leak_def D_def)

text \<open>(i.1) A2, S_in-ICI sessiz sizintiyi YASAKLAR (etkinin kendi olayinda).\<close>

lemma A2_forbids_inscope_silent_leak:
  assumes "A2 E \<iota>" "var \<iota> \<in> s_in E"
      and "effect_at E \<iota> To Tc i" and "silent_leak To Tc i"
  shows False
proof -
  from A2_manifests[OF assms(1) assms(2) assms(3)] have "D Dstar To Tc i" .
  with assms(4) show False by (simp add: silent_leak_iff_not_D)
qed

text \<open>(i.2) ASIL SONUC: her sessiz sizinti ZORUNLU olarak scope-disidir (S_out).\<close>

theorem silent_leak_only_out_of_scope:
  assumes "A2 E \<iota>" and "effect_at E \<iota> To Tc i" and "silent_leak To Tc i"
  shows "var \<iota> \<notin> s_in E"
  using A2_forbids_inscope_silent_leak[OF assms(1) _ assms(2,3)] by blast

text \<open>
  (i.3) Kontrapozitif: eger etki S_in'deyse ve A2 gecerliyse, o etki SESSIZ
  OLAMAZ -- D'nin en az bir clause'u ateslenir (gozlemlenebilir olmak zorunda).
\<close>

corollary inscope_effect_is_observable:
  assumes "A2 E \<iota>" "var \<iota> \<in> s_in E" "effect_at E \<iota> To Tc i"
  shows "soe_clause To Tc i \<or> timing_clause Dstar To Tc i"
  using A2_manifests[OF assms] by (simp add: D_def)


subsection \<open>6.2 HP witness insasi (App A item iv) -- ispatli\<close>

text \<open>
  W = S_in \ eff_vars (App A: "W = S_in \ observable(.)_i"). W2 (fixity-does-not-mask)
  kosulunun ihlal olasiligi = mask_prob = p_soe + p_conf, union-bound ile
  residual'a baglanir.
\<close>

definition witness_W :: "envelope \<Rightarrow> nat set" where
  "witness_W E = s_in E - eff_vars E"

definition mask_prob :: "envelope \<Rightarrow> intervention \<Rightarrow> real" where
  "mask_prob E \<iota> = p_soe E \<iota> + p_conf E \<iota>"

lemma witness_W_subset: "witness_W E \<subseteq> s_in E"
  by (simp add: witness_W_def)

\<comment> \<open>W2 union bound: mask olasiligi <= residual\<close>
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


subsection \<open>6.3 Pearl/HP korespondans predikatlari -- somut\<close>

text \<open>
  Effectiveness artik §3.1'deki top-level \<open>effective\<close> (do-operator anlambilimi);
  \<open>True\<close> placeholder'i kaldirildi. Burada yalnizca composition/AC predikatlari.
\<close>

\<comment> \<open>delta_A1-relaxed composition: cerceve-ici pertürbasyon delta_A1+alpha ile sinirli\<close>
definition composition_relaxed :: "envelope \<Rightarrow> intervention \<Rightarrow> bool" where
  "composition_relaxed E \<iota> \<longleftrightarrow> p_conf E \<iota> \<le> delta_A1 + alpha"

\<comment> \<open>HP AC1: etki D, Tcf'de olay i'de mevcut\<close>
definition ac1 :: "trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool" where
  "ac1 To Tc i \<longleftrightarrow> D Dstar To Tc i"

\<comment> \<open>HP AC2(a): counterfactual sensitivity -- D'nin dordunclu admissibility adimi\<close>
definition ac2a :: "trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool" where
  "ac2a To Tc i \<longleftrightarrow> D Dstar To Tc i"

\<comment> \<open>AC2(a)'nin TANIK-INDEKSLI hali (App A: "each independently witness")\<close>
definition ac2a_wit :: "ac2a_witness \<Rightarrow> trace \<Rightarrow> trace \<Rightarrow> nat \<Rightarrow> bool" where
  "ac2a_wit w To Tc i \<longleftrightarrow> witnesses w Dstar To Tc i"

lemma ac2a_iff_wit: "ac2a To Tc i \<longleftrightarrow> (\<exists>w. ac2a_wit w To Tc i)"
  unfolding ac2a_def ac2a_wit_def by (rule D_iff_witness)

\<comment> \<open>HP AC2(b): W1 (A4 ile fixity) + W ⊆ S_in + W2 (mask <= residual)\<close>
definition ac2b :: "envelope \<Rightarrow> intervention \<Rightarrow> bool" where
  "ac2b E \<iota> \<longleftrightarrow> A4 E \<iota> \<and> witness_W E \<subseteq> s_in E \<and> mask_prob E \<iota> \<le> residual"

lemma composition_relaxed_holds:
  assumes "A1 E \<iota>" shows "composition_relaxed E \<iota>"
  unfolding composition_relaxed_def using confounder_bound[OF assms] by simp

lemma ac2b_holds:
  assumes "A1 E \<iota>" "A4 E \<iota>" shows "ac2b E \<iota>"
  unfolding ac2b_def
  using assms(2) witness_W_subset w2_residual_bound[OF assms(1) assms(2)] by simp


subsection \<open>6.35 TANIK-BASINA hata zarfi -- YENI analitik icerik\<close>

text \<open>
  Paper'in "OR-clause asymmetry"si (CST doc sec:2.1): SOE clause DETERMINISTIK
  (A4 altinda FPR sifir), timing clause OLASILIKSAL (FPR <= alpha). Buradan
  paper'in prose'unda ACIKCA TURETILMEMIS bir sonuc cikar:

    Bir claim'in epistemik agirligi, HANGI TANIGIN atesledigine gore DEGISIR.

  Blanket `residual` yerine tanik-basina zarf tanimliyoruz:
    - Yapisal tanik: coincidence katkisi p_soe (A4 ile <= eps_SOE)
    - Zamanlama tanigi: coincidence katkisi p_tim (A3 ile <= alpha)
  Her ikisine de confounder katkisi p_conf (<= delta_A1 + alpha) eklenir.
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

text \<open>Yapisal tanigin zarfi tam olarak App A'nin `residual`'idir.\<close>

lemma wit_bound_structural_is_residual:
  assumes "A1 E \<iota>" "A4 E \<iota>"
  shows "wit_bound StructuralW E \<iota> \<le> residual"
  using wit_bound_structural[OF assms] unfolding residual_def by simp

text \<open>
  ANA SONUC: hangi tanik daha SIKI zarf verir? Tam karsilastirma kriteri
  eps_SOE ile alpha arasindaki iliskidir -- baska hicbir parametreye bagli degil.
\<close>

lemma structural_bound_tighter_iff:
  "(eps_SOE + delta_A1 + alpha \<le> delta_A1 + 2 * alpha) \<longleftrightarrow> eps_SOE \<le> alpha"
  by simp

text \<open>
  Okunusu (paper'in kalibrasyon rejimleriyle):
    - WITHIN-BOOT (N=998): eps_SOE <= 0.37%, alpha_realized = 0.61%
      => eps_SOE <= alpha  => YAPISAL tanik daha siki zarf verir.
    - CROSS-BOOT (N=34):   eps_SOE <= 10.4%, alpha_realized = 0.61%
      => eps_SOE > alpha   => kriter TERSINE doner; zamanlama tanigi daha siki.
  Yani "hangi tanik daha guclu" sorusunun cevabi kalibrasyon rejimine baglidir
  ve bu, tek bir esitsizlikle tam olarak karakterize edilir.
\<close>


subsection \<open>6.4 Kosullu CST teoremi (Teorem 1, => yonu) -- ispatli\<close>

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
  \<comment> \<open>D'den somut bir AC2(a) tanigi cikar\<close>
  from i(2) obtain w where w: "witnesses w Dstar To Tc i"
    using D_iff_witness by blast
  \<comment> \<open>tanigin kendi zarfi, iki tanik zarfinin maksimumuyla sinirli\<close>
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
  Residual zarfinin her admissible claim'de rapor edilen [0, residual] araliginda
  oldugunu ayrica gosteririz (App A: "reported per-claim").
\<close>

corollary cst_residual_reported:
  assumes "A1 E \<iota>" "A4 E \<iota>"
  shows "0 \<le> mask_prob E \<iota> \<and> mask_prob E \<iota> \<le> residual"
  using mask_prob_nonneg[OF assms] w2_residual_bound[OF assms] by simp


subsection \<open>6.45 Kapsam-TAMLIGI teoremi -- A2'nin gercek isi\<close>

text \<open>
  CST'nin iki AYRI yeterlilik yonu vardir; bunlari karistirmamak onemli:

    SOUNDNESS      (cst_conditional):   yayinlanan claim'ler saglamdir.
                                        Kullanir: A1, A3, A4.
    SCOPE-COMPLETENESS (asagidaki):     S_in icindeki etkiler KACIRILMAZ.
                                        Kullanir: A2.

  A2'nin cst_conditional'in hipotez listesinde gorunup ispatta cagrilmamasi bu
  yuzdendir -- A2 SOUNDNESS'a degil, TAMLIGA katki verir. Bunu ayri bir teorem
  olarak yazmak, A2'nin "olu hipotez" gorunmesini ortadan kaldirir ve rolunu
  kesinlestirir.
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
  Kontrapozitif okuma (scope-honesty): hic divergence yoksa, S_in icinde
  hicbir nedensel etki de YOKTUR. Yani CST'nin sessizligi, S_in uzerinde
  bilgilendiricidir -- S_out uzerinde ise HICBIR SEY soylemez.
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


subsection \<open>6.5 Sirali kompozisyon (Proposition 1) -- ispatli\<close>

text \<open>
  App A Proposition 1: n-adimli zincir admissible <=> her atomik adim admissible;
  delta_A1 union-bound ile birikir (O(n), bozunma yok). Zinciri, adim-basi
  admissibility booleanlarinin listesi olarak modelliyoruz.
\<close>

\<comment> \<open>Zincir admissible <=> tum atomik adimlar admissible (App A induction, biconditional)\<close>
lemma chain_iff_all_atomic:
  "list_all (\<lambda>b. b) steps \<longleftrightarrow> (\<forall>k < length steps. steps ! k)"
  by (simp add: list_all_length)

\<comment> \<open>n adim sonra birikmis delta_A1 zarfi\<close>
primrec accum_delta :: "nat \<Rightarrow> real" where
  "accum_delta 0 = 0"
| "accum_delta (Suc n) = accum_delta n + delta_A1"

lemma accum_delta_eq: "accum_delta n = of_nat n * delta_A1"
  by (induct n) (simp_all add: algebra_simps)

\<comment> \<open>Union bound: zarf adim sayisiyla lineer buyur, monoton -- bozunma yok\<close>
lemma accum_delta_mono: "accum_delta n \<le> accum_delta (Suc n)"
  using prob_nonneg(1) by simp

lemma accum_delta_linear_bound: "accum_delta n \<le> of_nat n * delta_A1"
  by (simp add: accum_delta_eq)


subsection \<open>6.55 Paralel sweep: TANIK-DUYARLI ensemble zarfi (b x Prop 1)\<close>

text \<open>
  DIKKAT -- eksen ayrimi. accum_delta (yukarida) SIRALI kompozisyonun delta_A1
  union-bound birikimidir (Prop 1). Bu alt-bolum ise PARALEL sweep icindir:
  App A "Scope clarification: sequential vs parallel ensembles" -- sweep = 33
  BAGIMSIZ atomik claim, her biri Korig'e karsi ayri dogrulanir, delta_A1
  per-claim sinirli, i uzerinde union-bound birikimi YOK, kapsam O(n).

  (b) adimi gosterdi ki her claim'in zarfi ATESLEYEN TANIGA baglidir. Bir
  sweep'te farkli claim'ler farkli taniklarla ateslenebilir; dolayisiyla
  ensemble-seviyesi (toplam) zarf TANIK-DUYARLI olmalidir ve naif "n * blanket"
  sinirindan DAHA SIKIDIR. Iste (b)'nin sweep'e tasinmasi budur.
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

text \<open>Kapali form: k yapisal + (n-k) zamanlama tanigi.\<close>

lemma sweep_ub_closed_form:
  "sweep_ub ws = of_nat (countS ws) * (eps_SOE + delta_A1 + alpha)
               + of_nat (countT ws) * (delta_A1 + 2 * alpha)"
proof (induct ws)
  case Nil show ?case by (simp add: sweep_ub_def)
next
  case (Cons w ws) thus ?case
    by (cases w) (simp_all add: sweep_ub_def wit_ub_def algebra_simps)
qed

text \<open>ANA SONUC: tanik-duyarli zarf, naif blanket biriktirmeden DAHA SIKI.\<close>

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
  GERCEK katki koprusu: her adimin olculen zarfi (wit_bound) kendi tanik ust
  sinirindan (wit_ub) kucuktur; dolayisiyla ensemble'in olculen toplam zarfi
  tanik-duyarli sweep_ub ile sinirlidir. Uc kademeli: olculen <= tanik-sayimli
  <= naif blanket.
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

text \<open>Uc kademeli sinir tek ifadede.\<close>

theorem sweep_three_level_bound:
  assumes "A1 E \<iota>" "A3 E \<iota>" "A4 E \<iota>"
  shows "sweep_actual E \<iota> ws \<le> sweep_ub ws
       \<and> sweep_ub ws \<le> of_nat (length ws) * blanket"
  using sweep_actual_le_ub[OF assms] sweep_ub_tighter by blast

text \<open>
  SESSIZ INPUT'LAR BEDAVA: ensemble zarfi yalnizca ADMISSIBLE claim sayisiyla
  olceklenir, taranan TOPLAM input sayisiyla DEGIL. Bu, scope-honesty'nin (d)
  ensemble seviyesindeki sonucudur -- D=false input'lar (None) zarfa hic girmez.
\<close>

lemma ensemble_envelope_bound:
  "sweep_ub (emitted_of xs) \<le> of_nat (length (emitted_of xs)) * blanket"
  by (rule sweep_ub_tighter)

lemma silent_inputs_free:
  "sweep_ub (emitted_of (None # xs)) = sweep_ub (emitted_of xs)"
  by simp

end  \<comment> \<open>locale cst_assumptions\<close>


subsection \<open>6.6 Locale tutarliligi: bir yorumlama (interpretation)\<close>

text \<open>
  Locale'in TUTARLI (celiskisiz) oldugunu, assumption'lari saglayan somut bir
  ornek yorumlama ile gosteririz: tum katkilar 0, tum sinirlar orta degerde.
  Bu, "vacuously true" olmadigini ve teoremlerin gercek bir modelde gecerli
  oldugunu dogrular.
\<close>

interpretation cst_trivial:
  cst_assumptions
    500                              \<comment> \<open>Dstar\<close>
    "1/10" "1/10" "1/20"             \<comment> \<open>delta_A1, eps_SOE, alpha\<close>
    "\<lambda>E \<iota>. True" "\<lambda>E \<iota>. True"         \<comment> \<open>A1, A2\<close>
    "\<lambda>E \<iota>. True" "\<lambda>E \<iota>. True"         \<comment> \<open>A3, A4\<close>
    "\<lambda>E \<iota>. 0" "\<lambda>E \<iota>. 0" "\<lambda>E \<iota>. 0"     \<comment> \<open>p_soe, p_tim, p_conf\<close>
    "\<lambda>E. {}"                         \<comment> \<open>eff_vars\<close>
    "\<lambda>E \<iota> To Tc i. soe_clause To Tc i"   \<comment> \<open>effect_at: etkiler YAPISAL olarak yansir (vacuous DEGIL)\<close>
  by unfold_locales (auto simp: D_def)


subsection \<open>6.7 Paper'in GERCEK kalibrasyon rejimleri -- sayisal instantiation\<close>

text \<open>
  Yukaridaki tanik-karsilastirma kriterini (structural_bound_tighter_iff)
  paper'in ILAN ETTIGI kalibrasyon degerleriyle instantiate ediyoruz.
  Boylece mekanizasyon soyut kalmiyor, dogrudan extp.tex'in rakamlarina baglaniyor.

  Kaynak: extp.tex sec:capsep / sec:soe / sec:mi
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
    "\<lambda>E \<iota> To Tc i. soe_clause To Tc i"   \<comment> \<open>effect_at: etkiler YAPISAL olarak yansir (vacuous DEGIL)\<close>
  by unfold_locales (auto simp: D_def)

interpretation cst_crossboot:
  cst_assumptions
    9077
    "1040/10000" "1040/10000" "61/10000"
    "\<lambda>E \<iota>. True" "\<lambda>E \<iota>. True" "\<lambda>E \<iota>. True" "\<lambda>E \<iota>. True"
    "\<lambda>E \<iota>. 0" "\<lambda>E \<iota>. 0" "\<lambda>E \<iota>. 0"
    "\<lambda>E. {}"
    "\<lambda>E \<iota> To Tc i. soe_clause To Tc i"   \<comment> \<open>effect_at: etkiler YAPISAL olarak yansir (vacuous DEGIL)\<close>
  by unfold_locales (auto simp: D_def)

text \<open>
  WITHIN-BOOT: eps_SOE (0.37%) <= alpha (0.61%)  =>  YAPISAL tanik daha siki.
  Zarflar: yapisal 1.35%  vs  zamanlama 1.59%.
\<close>

lemma withinboot_criterion: "(37/10000 :: real) \<le> 61/10000"
  by simp

lemma withinboot_structural_tighter:
  "(37/10000 :: real) + 37/10000 + 61/10000 \<le> 37/10000 + 2 * (61/10000)"
  by simp

text \<open>
  CROSS-BOOT: eps_SOE (10.4%) > alpha (0.61%)  =>  kriter TERSINE doner,
  ZAMANLAMA tanigi daha siki. Zarflar: yapisal 21.41%  vs  zamanlama 11.62%.
\<close>

lemma crossboot_criterion: "\<not> ((1040/10000 :: real) \<le> 61/10000)"
  by simp

lemma crossboot_timing_tighter:
  "(1040/10000 :: real) + 2 * (61/10000) \<le> 1040/10000 + 1040/10000 + 61/10000"
  by simp

text \<open>
  Bu iki rejimin ZIT sonuc vermesi, tanik ayrimini kozmetik olmaktan cikarir:
  bir CST claim'inin epistemik agirligi hem HANGI TANIGIN atesledigine hem de
  HANGI KALIBRASYON REJIMINDE calisildigina baglidir. Downstream tuketiciler
  (mitigation verification, counterfactual fuzzing) blanket `residual` yerine
  tanik-basina zarfi kullanarak daha siki -- ve dogru rejimde daha DURUST --
  bir sinir raporlayabilir.
\<close>


subsection \<open>6.75 Karisik sweep: tanik-duyarli zarf KESIN daha siki (sayisal)\<close>

text \<open>
  (f)'in somut getirisi: within-boot rejiminde, biri yapisal biri zamanlama
  tanigiyla ateslenen 2-claim'lik bir sweep icin tanik-duyarli toplam zarf
  2.94%, naif "n * blanket" ise 3.18% -- yani KESIN olarak daha siki (esit degil).
  Bir S1/T1 sweep'inin uctan uca kapsam haritasinda (paper Fig. sweep) bu fark,
  claim sayisiyla dogru orantili olarak buyur.
\<close>

lemma withinboot_sweep_strictly_tighter:
  "cst_withinboot.sweep_ub [StructuralW, TimingW]
     < of_nat (length [StructuralW, TimingW]) * cst_withinboot.blanket"
  by (simp add: cst_withinboot.sweep_ub_def cst_withinboot.wit_ub_def
                cst_withinboot.blanket_def)

text \<open>Kapali-form dogrulamasi: sweep_ub [S,T] = 294/10000.\<close>

lemma withinboot_sweep_value:
  "cst_withinboot.sweep_ub [StructuralW, TimingW] = 294/10000"
  by (simp add: cst_withinboot.sweep_ub_def cst_withinboot.wit_ub_def)

text \<open>Naif blanket birikimi = 318/10000; fark = 24/10000 (claim basina ~0.12%).\<close>

lemma withinboot_blanket_value:
  "of_nat (length [StructuralW, TimingW]) * cst_withinboot.blanket = 318/10000"
  by (simp add: cst_withinboot.blanket_def)

text \<open>
  Homojen sweep'te esitlik: tum claim'ler ayni (en kotu) tanikla ateslenirse
  tanik-duyarli zarf naif blanket'e ESITTIR -- yani siklik kazanci tam olarak
  tanik KARISIMINDAN gelir, baska bir yerden degil.
\<close>

lemma withinboot_homogeneous_equality:
  "cst_withinboot.sweep_ub [TimingW, TimingW]
     = of_nat (length [TimingW, TimingW]) * cst_withinboot.blanket"
  by (simp add: cst_withinboot.sweep_ub_def cst_withinboot.wit_ub_def
                cst_withinboot.blanket_def)


subsection \<open>6.8 GERCEK sweep verisine baglama (adim h)\<close>

text \<open>
  extp.tex sec:eval-demo-sweep gercek sonucu:
    - 33 input taraniyor (0xDEAD + 16 low-byte + 14 wide + 2 distractor).
    - Divergence sayisi 1/33: yalnizca 0xDEAD ateslendi (SOE clause; RIP 0x10016,
      RAX 0x80000008). Diger 32'si default-path, SOE clause SESSIZ => D=false
      => ADMISSIBLE CLAIM YOK.
    - Tum divergence SOE-clause; TIMING tanigi hic yok.
  Bunu modele birebir kodluyoruz.
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
  Ensemble zarfi, GERCEK kalibrasyonla. WITHIN-BOOT: yalnizca 1 yapisal claim
  => zarf = eps_SOE + delta_A1 + alpha = 1.35%.
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

text \<open>Naif taranan-input siniri = 33 * 1.59% = 52.47%.\<close>

lemma dead_sweep_naive_swept_value:
  "of_nat (length dead_sweep) * cst_withinboot.blanket = 5247/10000"
  by (simp add: dead_sweep_total cst_withinboot.blanket_def)

text \<open>
  Somut silent-leak: ex_silent'teki +400-cycle fark, gercek Delta*=9077 (within-boot)
  altinda sub-esik => her iki clause sessiz => silent_leak. (adim i, somut baglanti)
\<close>

lemma ex_silent_is_silent_leak_withinboot:
  "cst_withinboot.silent_leak ex_orig ex_silent 0"
  by (simp add: cst_withinboot.silent_leak_def soe_clause_def timing_clause_def
                ex_orig_def ex_silent_def ev_def)

text \<open>
  Dolayisiyla (silent_leak_only_out_of_scope ile): boyle bir sub-Delta* etki, A2
  altinda ancak S_out'ta yasayabilir -- MI silent-leak sinifinin CMD-future-class'a
  ertelenmesinin makine-kontrollu cekirdegi.
\<close>

text \<open>
  ASIL SONUC (scope-honesty x ensemble): 33-input'luk sweep'in zarfi, taranan
  input sayisiyla DEGIL, admissible claim sayisiyla (1) olceklenir. Naif "her
  taranan input bir yuk tasir" gorusu 33 * blanket = 52.47% verirdi; gercek zarf
  1.35% -- ~39 kat daha siki, cunku 32 sessiz input BEDAVA.
\<close>

lemma dead_sweep_envelope_vs_naive_swept:
  "cst_withinboot.sweep_ub (emitted_of dead_sweep)
     < of_nat (length dead_sweep) * cst_withinboot.blanket"
  using dead_sweep_envelope_withinboot dead_sweep_naive_swept_value by simp


section \<open>7. FAZ 3 arayuz iskeleti (lifting) -- YUKUMLULUK IZOLE, ACIK KAPATILMAZ\<close>

text \<open>
  >>> DURUSTLUK NOTU (kritik). Bu bolum lifting acigini KAPATMAZ. Gercek kapatma
  L4.verified'in devasa Isabelle ispatina baglanmayi ve VMM/VT-x katmanini
  formalize etmeyi gerektirir (cok-yillik; ve yalnizca K_verified'i kapsar).
  Burada yapilan: (1) lifting'in TIPLI ARAYUZUNU tanimlamak; (2) seL4'un
  saglamasi gereken TEK teoremi -- K_verified operasyonlarinin external
  atomicity'si -- acik, ISIMLI bir locale ASSUMPTION olarak IZOLE etmek;
  (3) bu assumption VERILDIGINDE A1'in K_verified icin delta_A1=0 (kosulsuz
  modularity) ile yapisal olarak ciktigini ispatlamak; (4) K_extended'in bu
  assumption'in guard'i disinda kaldigini, dolayisiyla ampirik kaldigini
  gostermek. Assumption ISPATLANMAZ -- multi-year delik tam olarak orasidir;
  biz onu kapatmiyor, TEK ve isaretli bir yukumluluge indirgeyip sinirstiriyoruz.
\<close>

typedecl sel4_astate   \<comment> \<open>seL4 soyut makine durumu (opak; gercek modeli L4.verified'de)\<close>

consts
  lift :: "sel4_astate \<Rightarrow> observable"   \<comment> \<open>soyut durum -> EXTp VMCS-observable yuzeyi\<close>

datatype kop =
    Create | Copy | Revoke | Destroy        \<comment> \<open>K_verified (L4.verified kapsaminda)\<close>
  | MapEPT | Unmap | ReadVMCS | WriteVMCS    \<comment> \<open>K_extended (verified kapsam DISI)\<close>

definition k_verified :: "kop set" where
  "k_verified = {Create, Copy, Revoke, Destroy}"

definition k_extended :: "kop set" where
  "k_extended = {MapEPT, Unmap, ReadVMCS, WriteVMCS}"

lemma k_partition_disjoint: "k_verified \<inter> k_extended = {}"
  by (auto simp: k_verified_def k_extended_def)

lemma k_partition_complete: "k_verified \<union> k_extended = UNIV"
  by (auto simp: k_verified_def k_extended_def) (case_tac x, auto)

text \<open>
  seL4 arayuz locale'i. `op_authority op` = op'un dokunabildigi degisken kumesi;
  `fwk_vars` = framework-internal (K_fwk) degiskenler. Tek assumption:
  K_verified op'lari framework-internal duruma DOKUNMAZ (external atomicity'nin
  operasyonel karsiligi). Bu, L4.verified'in SAGLADIGI seydir; BURADA ISPATLANMAZ.
\<close>

locale sel4_lifting =
  fixes op_authority :: "kop \<Rightarrow> nat set"
    and fwk_vars      :: "nat set"
  assumes verified_no_fwk_touch:
    "\<And>op. op \<in> k_verified \<Longrightarrow> op_authority op \<inter> fwk_vars = {}"
    \<comment> \<open>^ L4.verified external-atomicity yukumlulugu; ACIK, tek delik.\<close>
begin

text \<open>
  (g.1) Assumption verildiginde, A1'in K_verified icin KOSULSUZ hali (delta=0):
  intervention K_verified op'u ise, framework-internal duruma etki EDEMEZ.
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
  (g.2) K_extended, assumption'in guard'i DISINDADIR: bu locale onlar hakkinda
  HICBIR sey soylemez. Boyle bir op'un framework'e dokundugu bir dunya
  TUTARLIDIR (asagidaki yorumlama) -- yani K_extended icin delta=0 CIKMAZ,
  ampirik kalir. Bu, paper'in K_verified (kosulsuz) / K_extended (ampirik)
  ayrimin makine-kontrollu karsiligidir.
\<close>

lemma verified_guard_excludes_extended:
  "MapEPT \<notin> k_verified"
  by (simp add: k_verified_def)

end  \<comment> \<open>locale sel4_lifting\<close>

text \<open>
  (g.3) TUTARLILIK + K_extended'in kapsanmadiginin KANITI: oyle bir yorumlama
  var ki (a) assumption saglanir (locale bos degil), (b) bir K_extended op'u
  framework'e DOKUNUR. Yani arayuz tutarli AMA K_extended'i kurtarmiyor.
\<close>

definition demo_auth :: "kop \<Rightarrow> nat set" where
  "demo_auth op = (if op \<in> k_verified then {} else {0})"

interpretation sel4_demo:
  sel4_lifting demo_auth "{0}"
  by unfold_locales (simp add: demo_auth_def)

lemma extended_can_touch_fwk:
  "demo_auth MapEPT \<inter> {0} \<noteq> {}"    \<comment> \<open>K_extended framework'e dokunur\<close>
  by (simp add: demo_auth_def k_verified_def k_extended_def)

lemma verified_cannot_touch_fwk:
  "demo_auth Create \<inter> {0} = {}"      \<comment> \<open>K_verified dokunmaz\<close>
  by (simp add: demo_auth_def k_verified_def)

text \<open>
  >>> OZET. Yukaridaki teoremler lifting'i KAPATMAZ. Kapatma =
  `verified_no_fwk_touch` assumption'ini L4.verified'in gercek atomicity
  teoreminden TURETMEK (ve `lift`/`sel4_astate`'i gercek seL4 makine modeline
  baglamak). O is bu dosyada YOK ve cok-yillik. Burada yalnizca: yukumluluk
  tek ve isimli hale getirildi, ondan cikanlar (K_verified delta=0) ispatlandi,
  ve K_extended'in kapsam disi kaldigi gosterildi. Kosullu CST teoremi (Faz 2)
  bu bolumun HICBIRINE ihtiyac duymaz; bu bolum yalnizca A1'in bir alt-kumesini
  ampirik olmaktan cikarmanin fiyat etiketini tipli olarak sergiler.
\<close>

section \<open>8. Iki "prose" kosesinin kapatilmasi: W-formunda composition + trace-zincirli Prop 1\<close>

text \<open>
  Statement-fidelity denetimi (2026-09-01) kagit ispatinda iki noktayi "prose" birakmisti:
    (F2) App A item (ii): Pearl composition'in delta_A1-relaxed hali paper'da K_fwk
         uzerindeki W degiskenleri ve |W_cf - W_orig| perturbasyonu ile ifade ediliyor;
         mekanizasyon bunu yalnizca confounder bound (composition_relaxed) olarak
         MODELLEMISTI.
    (F5) Prop 1 sirali kompozisyon: paper'da T_cf^(k) bir sonraki adimin BASELINE'i;
         mekanizasyon yalnizca n*delta_A1 aritmetigini tasiyordu.
  Bu bolum ikisini de paper'daki ifadeye birebir karsilik gelecek sekilde kapatir.
  Antecedent disiplini korunur: olasiliklar (p_pert) soyut reel parametre olarak girer.
\<close>

subsection \<open>8.1 Holding W: yapisal kisim (locale disi)\<close>

text \<open>
  hold W \<sigma>o \<sigma>: valuation \<sigma>'da W kumesindeki degiskenleri T_orig'deki degerlerine
  (\<sigma>o) sabitler -- Pearl/HP'nin "W = w_orig tutulurken" islemi.
\<close>

definition hold :: "nat set \<Rightarrow> valuation \<Rightarrow> valuation \<Rightarrow> valuation" where
  "hold W \<sigma>o \<sigma> = (\<lambda>v. if v \<in> W then \<sigma>o v else \<sigma> v)"

text \<open>Her W-degiskeninde |W_cf - W_orig| \<le> Dstar (App A: "perturbation bounded by Dstar on each W").\<close>

definition pert_bounded :: "nat \<Rightarrow> nat set \<Rightarrow> valuation \<Rightarrow> valuation \<Rightarrow> bool" where
  "pert_bounded Dstar W \<sigma>o \<sigma>c \<longleftrightarrow> (\<forall>w\<in>W. \<bar>int (\<sigma>c w) - int (\<sigma>o w)\<bar> \<le> int Dstar)"

lemma hold_in:  "v \<in> W \<Longrightarrow> hold W \<sigma>o \<sigma> v = \<sigma>o v" by (simp add: hold_def)
lemma hold_out: "v \<notin> W \<Longrightarrow> hold W \<sigma>o \<sigma> v = \<sigma> v" by (simp add: hold_def)

text \<open>
  Pearl composition, KATI form: W zaten dogal degerinde ise (W_x = w), W'yi tutmak
  sonucu degistirmez -- do(x') tek basina ile do(x') + hold W AYNI valuation'i verir.
  Tek yapisal on-kosul: mudahale degiskeni W'nin DISINDA (CapSep: K_int \<inter> K_fwk = {}).
  Aksi halde hold mudahaleyi geri alirdi.
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

text \<open>Effectiveness W tutulurken de korunur: hold, do(x')'i geri almaz.\<close>

lemma hold_preserves_effectiveness:
  assumes "var \<iota> \<notin> W"
  shows "hold W \<sigma>o (apply_iv \<iota> \<sigma>c) (var \<iota>) = newval \<iota>"
  using assms by (simp add: hold_def apply_iv_def)

text \<open>
  delta_A1-RELAXED form, yapisal kisim: W tam dogal degerinde OLMASA bile, W tutulan ve
  tutulmayan iki do(x') sonucu (a) W disinda (X dahil) ozdes, (b) W icinde her
  koordinatta en fazla Dstar farkli -- pert_bounded altinda.
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


subsection \<open>8.2 Olasiliksal kisim: locale cst_composition (A1'in sembolik icerigi)\<close>

text \<open>
  App A, A1'in sembolik hali: her W \<in> K_fwk icin Pr[|W_cf - W_orig| > Dstar] \<le> delta_A1.
  p_pert E \<iota> w bu olasiligin soyut reel parametresi (olculur, ispatlanmaz -- antecedent
  disiplini). Ikinci assumption CapSep'in yapisal iddiasi K_int \<inter> K_fwk = {}'nin
  mudahale-degiskeni duzeyindeki hali: A1 altinda hedef X, K_fwk'nin disindadir.
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
  App A item (ii), paper'daki ifadeyle birebir: "for all W in K_fwk, the outcome under
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

text \<open>W tutulurken do(x') etkisi korunur (effectiveness composition altinda kaybolmaz).\<close>

corollary composition_W_keeps_effect:
  assumes "A1 E \<iota>"
  shows "hold fwk_vars \<sigma>o (apply_iv \<iota> \<sigma>c) (var \<iota>) = newval \<iota>"
  by (rule hold_preserves_effectiveness[OF A1_target_outside_fwk[OF assms]])

text \<open>Kati form geri kazanilir: delta_A1 \<rightarrow> 0 limitinde perturbasyon olasiligi 0 (App A "Recovery of strict form").\<close>

theorem composition_strict_recovered:
  assumes "A1 E \<iota>" and "delta_A1 = 0" and "w \<in> fwk_vars"
  shows "p_pert E \<iota> w = 0"
  using A1_pert_per_var[OF assms(1) assms(3)] assms(2) by linarith

text \<open>Sonlu K_fwk uzerinde union bound: toplam perturbasyon kutlesi \<le> |K_fwk| * delta_A1.\<close>

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
  Kosullu CST teoremi, composition'in W-formuyla: eski confounder-bound modeli
  (composition_relaxed) KALIR, W-formu ona EKLENIR -- teorem ikisini birden verir.
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
  Tutarlilik + vacuous olmadiginin kaniti: K_fwk = {0}, A1 = "hedef 0 degil".
  A1 hem saglanabilir (var = 7) hem ihlal edilebilir (var = 0); K_fwk bos degil.
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


subsection \<open>8.3 Prop 1, trace-zincirli: T_cf^(k) bir sonraki adimin baseline'i\<close>

context cst_assumptions
begin

text \<open>
  Zincir = mudahale listesi + (n+1) trace: Ts!0 = T_orig, Ts!(k+1) = k'inci adimin
  T_cf'i; adim k+1 Ts!(k+1)'i BASELINE alir (App A tumevarim adimi). Bu,
  chain_iff_all_atomic'teki boolean-listesi soyutlamasinin yerini alan GERCEK zincir.
  Siralama iddianin PARCASIDIR: rev \<iota>s icin ayni Ts anlamli degildir (baska bir
  yurutme, baska trace'ler) -- komutatiflik iddia edilmez (App A).
\<close>

fun chain_ok :: "envelope \<Rightarrow> intervention list \<Rightarrow> bool \<Rightarrow> trace list \<Rightarrow> bool" where
  "chain_ok E [] ok Ts = (length Ts = 1)"
| "chain_ok E (\<iota> # \<iota>s) ok (To # Tc # Ts) =
     (admissible Dstar E \<iota> ok To Tc \<and> chain_ok E \<iota>s ok (Tc # Ts))"
| "chain_ok E (\<iota> # \<iota>s) ok Ts = False"

text \<open>Prop 1'in GERCEK ifadesi: zincir admissible \<longleftrightarrow> her atomik adim, KENDI baseline'iyla, admissible.\<close>

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
  App A tumevarim adimi, birebir: zinciri bir adim uzatmak = SON T_cf'i baseline alan
  bir atomik adim eklemek. "Applying Theorem 1 to the atomic step with T_cf^(n) as the
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

text \<open>Zincirin HER adimi icin kosullu CST sonucu (Teorem 1 adim adim, kendi baseline'inda).\<close>

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
  A1^(n+1) \<le> A1^(n) + delta_A1 (App A): zincir bir adim uzadiginda birikmis A1 zarfi
  tam olarak delta_A1 artar; toplam n * delta_A1 (accum_delta_eq).
\<close>

lemma chain_delta_step:
  "accum_delta (length (\<iota>s @ [\<iota>])) = accum_delta (length \<iota>s) + delta_A1"
  by simp

text \<open>
  Zincirin tanik zarflari: adimlar BAGIMLI olsa da union bound gecerlidir (bagimsizlik
  varsayilmaz -- App A "tighter bounds under independence are not asserted").
  Toplam \<le> tanik-duyarli sweep_ub \<le> n * blanket.
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
  Somut 2-adimli zincir (within-boot rejimi): T0 = ex_orig, T1 rax'i degistirir,
  T2 T1'in rax'ini bir daha degistirir; ikinci adimin baseline'i T1'dir.
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

text \<open>Baseline kaymasi somut: ikinci adim T_orig'e degil T1'e karsi olculur.\<close>

lemma chain_demo_baseline_shift:
  "cst_withinboot.chain_ok ch_E [ch_iv1, ch_iv2] True [ex_orig, ch_T1, ch_T2]
   \<longleftrightarrow> admissible 9077 ch_E ch_iv1 True ex_orig ch_T1 \<and> admissible 9077 ch_E ch_iv2 True ch_T1 ch_T2"
  by (simp add: cst_withinboot.chain_ok.simps)

end
