theory TestGen
  imports IsaCircus
  keywords "generate_tests_rct" :: thy_decl
    and "RoboChart" "Mutants" "RoboWorld" "Iterations"
begin

declare [[literal_variables=true]]

section \<open>RescueDrone RoboChart and mutants\<close>

class hastock =
  fixes tock_prism :: "unit \<Longrightarrow>\<^sub>\<triangle> 'a"
  assumes tock_prism_wb: "wb_prism tock_prism"

print_theorems

dataspace tock =
  channels
    tock :: unit

context tock
begin

fun Wait :: "nat \<Rightarrow> ('ch, 'st) action" where
  "Wait 0 = Skip" |
  "Wait (Suc n) = tock \<rightarrow> (Wait n)"

definition await_trigger :: "('ch, 'st) action \<Rightarrow> ('ch, 'st) action" where
  "await_trigger P = \<mu> (\<lambda> X. P \<box> tock \<rightarrow> X)"

end

datatype InOut = In | Out

dataspace rescueDronePlatform = tock +
  channels
    moveCall :: nat
    turnBackCall :: unit
    found :: InOut
    origin :: InOut
    takeoff :: InOut
    land :: InOut

dataspace rescueDroneRoboChart = rescueDronePlatform +
  constants
    DELIVERY :: nat
    LV :: nat
    TOP :: nat
    TURN :: nat

(*chantype rescueDroneEvents =
  moveCall :: nat
  turnBackCall :: unit
  found :: InOut
  origin :: InOut
  takeoff :: InOut
  land :: InOut
  tock :: unit
*)

context rescueDroneRoboChart
begin

(*
instantiation rescueDroneEvents :: hastock
begin
definition [simp]: "tock_prism_rescueDroneEvents \<equiv> tock"

print_methods

instance by (intro_classes, simp)
end
*)

lemma "Wait(1) = tock \<rightarrow> Skip"
  by simp

definition RescueDrone :: "('ch, 'st) action" where
  "RescueDrone = \<mu> (\<lambda> X.
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    X)"

definition RescueDrone_mTransTarget_Output0 :: "('ch, 'st) action" where
  "RescueDrone_mTransTarget_Output0 = \<mu> (\<lambda> X.
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    X)"

definition RescueDrone_mTransTarget_Output1 :: "('ch, 'st) action" where
  "RescueDrone_mTransTarget_Output1 = \<mu> (\<lambda> X.
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    X)"

definition RescueDrone_mTransTarget_Output2 :: "('ch, 'st) action" where
  "RescueDrone_mTransTarget_Output2 = \<mu> (\<lambda> X.
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    X)"

definition RescueDrone_mTransTarget_Output3 :: "('ch, 'st) action" where
  "RescueDrone_mTransTarget_Output3 = 
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; \<mu> (\<lambda> X.
      (Wait(DELIVERY)) ;;
      ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
      X)"

definition RescueDrone_mTransTarget_Output4 :: "('ch, 'st) action" where
  "RescueDrone_mTransTarget_Output4 = \<mu> (\<lambda> X.
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    X)"

definition RescueDrone_mTransTarget_Output5 :: "('ch, 'st) action" where
  "RescueDrone_mTransTarget_Output5 = \<mu> (\<lambda> X.
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    X)"

definition RescueDrone_mTransTarget_Output6 :: "('ch, 'st) action" where
  "RescueDrone_mTransTarget_Output6 = \<mu> (\<lambda> X.
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    X)"

definition RescueDrone_mTransTarget_Output7 :: "('ch, 'st) action" where
  "RescueDrone_mTransTarget_Output7 = \<mu> (\<lambda> X.
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    X)"

definition RescueDrone_mTransTarget_Output8 :: "('ch, 'st) action" where
  "RescueDrone_mTransTarget_Output8 = \<mu> (\<lambda> X.
    await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; 
    (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
    await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
    (Wait(DELIVERY)) ;;
    ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
    X)"

definition RescueDrone_mTransTarget_Output9 :: "('ch, 'st) action" where
  "RescueDrone_mTransTarget_Output9 = 
    (takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; \<mu> (\<lambda> X.
      (moveCall\<^bold>.LV \<rightarrow> Skip) ;;
      await_trigger(found\<^bold>.In \<rightarrow> (land\<^bold>.Out \<rightarrow> Skip)) ;; 
      (Wait(DELIVERY)) ;;
      ((takeoff\<^bold>.Out \<rightarrow> Wait(TOP)) ;; (turnBackCall \<rightarrow> Wait(TURN)) ;; (moveCall\<^bold>.LV \<rightarrow> Skip)) ;;
      await_trigger((origin\<^bold>.In \<rightarrow> (turnBackCall \<rightarrow> Wait(TURN))) ;; (land\<^bold>.Out \<rightarrow> Skip)) ;;
      X)"

lemmas rct_defs = RescueDrone_def RescueDrone_mTransTarget_Output0_def RescueDrone_mTransTarget_Output1_def
  RescueDrone_mTransTarget_Output2_def RescueDrone_mTransTarget_Output3_def
  RescueDrone_mTransTarget_Output4_def RescueDrone_mTransTarget_Output5_def
  RescueDrone_mTransTarget_Output6_def RescueDrone_mTransTarget_Output7_def
  RescueDrone_mTransTarget_Output8_def RescueDrone_mTransTarget_Output9_def

end



section \<open>RescueDrone RoboWorld\<close>

no_notation disj (infixr "|" 30)

(* extra CyPhyCircus action types needed for RoboWorld *)
axiomatization
  cevol :: "('s \<Rightarrow> 's) \<Rightarrow> 's pred \<Rightarrow> ('e, 's) action" and
  cinterrupt_cond :: "('e, 's) action \<Rightarrow> 's pred \<Rightarrow> ('e, 's) action" 
where
  cevol_cinterrupt: "cinterrupt_cond (cevol e p) q = cevol e (p \<and> \<not> q)" and
  cevol_assumeI: "cevol e p = cevol e p ;; cassume (\<not> p)"

lemma "(\<^bold>v:[p, q]) = (\<^bold>v:[p, q] ;; {q}\<^sub>C)"
  by (transfer, rdes_eq)

syntax
  "_cevol" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("[\<Lambda> _ | _ ]")
  "_cevol_nopred" :: "logic \<Rightarrow> logic" ("[\<Lambda> _ ]")
  "_cinterrupt_cond" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<triangle>\<^sub>p" 55)

translations
  "_cevol_nopred e" == "CONST cevol e true"
  "_cevol e p" == "CONST cevol e (p)\<^sub>e"
  "P \<triangle>\<^sub>p e" == "CONST cinterrupt_cond P (e)\<^sub>e"

lemma "[\<Lambda> \<sigma> | p ] = [\<Lambda> \<sigma> | p ] ;; {\<not> p}\<^sub>C"
  by (subst cevol_assumeI, simp add: atomize_upred)

definition oriToVec :: "real*real*real \<Rightarrow> real*real*real" where
  "oriToVec = (\<lambda>(yaw, pitch, roll). ((cos yaw) * (cos pitch), (sin yaw) * (cos pitch), -sin pitch))"

lemma "oriToVec (pi/2, 0, 0) = (0, 1, 0)"
  unfolding oriToVec_def by auto

lemma "oriToVec (pi, 0, 0) = (-1, 0, 0)"
  unfolding oriToVec_def by auto

lemma "oriToVec (0, pi, 0) = (-1, 0, 0)"
  unfolding oriToVec_def by auto

lemma "oriToVec (pi, pi, 0) = (1, 0, 0)"
  unfolding oriToVec_def by auto

definition scalarMult3 :: "real \<Rightarrow> real*real*real \<Rightarrow> real*real*real" (infixl \<open>*\<^sub>3\<close> 70) where
  "scalarMult3 = (\<lambda> a (x, y, z). (a * x, a * y, a * z))"

abbreviation x :: "real \<Longrightarrow> real * real * real" where "x \<equiv> fst\<^sub>L"
abbreviation y :: "real \<Longrightarrow> real * real * real" where "y \<equiv> fst\<^sub>L ;\<^sub>L snd\<^sub>L"
abbreviation z :: "real \<Longrightarrow> real * real * real" where "z \<equiv> snd\<^sub>L ;\<^sub>L snd\<^sub>L"

definition dist :: "real*real*real \<Rightarrow> real*real*real \<Rightarrow> real" where
  "dist = (\<lambda> (x1, y1, z1) (x2, y2, z2). sqrt (x1*x2 + y1*y2 + z1*z2))"

record arena =
    origin :: "(real * real * real) set"
    target :: "(real * real * real) set"

dataspace rescueDroneRoboWorld = rescueDronePlatform +
  constants
    tockLength :: real
    timeStep :: real
    arena :: arena
  assumes
    positive_tock: "tockLength > 0" and
    positive_step: "timeStep > 0" and
    origin_target_distance: "\<forall> x\<in>origin arena. \<forall> y\<in>target arena. dist x y \<ge> 1"
  variables
    pos :: "real * real * real"
    vel :: "real * real * real"
    acc :: "real * real * real"
    ori :: "real * real * real"
    angVel :: "real * real * real"
    angAcc :: "real * real * real"
    foundTrig :: bool
    originTrig :: bool
    stepTimer :: real
    tockTimer :: real
  channels
    foundTriggered :: bool
    originTriggered :: bool
    setVel :: "real * real * real"
    setAngVel :: "real * real * real"
    proceed :: unit

context rescueDroneRoboWorld
begin

(* alphabet rescueDroneRoboWorld =
  pos :: "real * real * real"
  vel :: "real * real * real"
  acc :: "real * real * real"
  ori :: "real * real * real"
  angVel :: "real * real * real"
  angAcc :: "real * real * real"
*)

term "[\<Lambda> [pos \<leadsto> vel, vel \<leadsto> acc, ori \<leadsto> angVel, angVel \<leadsto> angAcc] | pos:z \<ge> 0 ]"
term "[\<Lambda> [pos \<leadsto> vel, vel \<leadsto> acc, ori \<leadsto> angVel, angVel \<leadsto> angAcc] ]"

lemma "[\<Lambda> [pos \<leadsto> vel, vel \<leadsto> acc, ori \<leadsto> angVel, angVel \<leadsto> angAcc] | pos:z \<ge> 0 ]
  = [\<Lambda> [pos \<leadsto> vel, vel \<leadsto> acc, ori \<leadsto> angVel, angVel \<leadsto> angAcc] ] \<triangle>\<^sub>p (pos:z < 0)"
  by (auto simp add: cevol_cinterrupt, pred_auto add: fun_Compl_def linorder_not_less)


definition EnvironmentInit :: "('ch, 'st) action" where
  "EnvironmentInit = \<^bold>v:[True, pos \<in> origin arena]"

definition RobotMovement :: "('ch, 'st) action" where
  "RobotMovement = [\<Lambda> [pos \<leadsto> vel, vel \<leadsto> acc, ori \<leadsto> angVel, angVel \<leadsto> angAcc, stepTimer \<leadsto> 1]]"

definition RobotMovementAction :: "('ch, 'st) action" where
  "RobotMovementAction = RobotMovement \<triangle>\<^sub>p (stepTimer \<ge> timeStep)"

definition found_InputEventTrigger :: "('ch, 'st) action" where
  "found_InputEventTrigger = foundTriggered\<^bold>!(pos \<in> target arena) \<rightarrow> Skip"

definition origin_InputEventTrigger :: "('ch, 'st) action" where
  "origin_InputEventTrigger = originTriggered\<^bold>!(pos \<in> target arena) \<rightarrow> Skip"

definition InputTriggers :: "('ch, 'st) action" where
  "InputTriggers = found_InputEventTrigger \<lbrakk> \<^bold>0 \<parallel> \<^bold>0 \<rbrakk> origin_InputEventTrigger"

definition Communication :: "('ch, 'st) action" where
  "Communication = \<mu> (\<lambda> X.
    setVel\<^bold>?v \<rightarrow> (vel := v) ;; X
     \<box>
    setAngVel\<^bold>?av \<rightarrow> (angVel := av) ;; X
     \<box>
    proceed \<rightarrow> Skip)"

definition EnvironmentLoop :: "('ch, 'st) action" where
  "EnvironmentLoop = EnvironmentInit ;; \<mu> (\<lambda> X.
    RobotMovementAction ;;
    InputTriggers ;;
    Communication ;;
    (stepTimer := 0) ;;
    if tockTimer \<ge> tockLength then tockTimer := 0 else Skip fi)"

definition found_Buffer :: "('ch, 'st) action" where
  "found_Buffer =
    foundTrig := False ;; \<mu> (\<lambda> X. (
      foundTriggered\<^bold>?b \<rightarrow> (foundTrig := b)
       \<box>
      (foundTrig) \<^bold>& found\<^bold>.In \<rightarrow> Skip
    ) ;; X)"

definition origin_Buffer :: "('ch, 'st) action" where
  "origin_Buffer =
    originTrig := False ;; \<mu> (\<lambda> X. (
      originTriggered\<^bold>?b \<rightarrow> (originTrig := b)
       \<box>
      (originTrig) \<^bold>& origin\<^bold>.In \<rightarrow> Skip
    ) ;; X)"

definition InputBuffers :: "('ch, 'st) action" where
  "InputBuffers = found_Buffer \<lbrakk> foundTrig \<parallel> originTrig \<rbrakk> origin_Buffer"

definition Environment :: "('ch, 'st) action" where
  "Environment =
    EnvironmentLoop
      \<lbrakk> (pos, vel, acc, ori, angVel, angAcc, stepTimer, tockTimer) 
        \<parallel> \<lbrace> foundTriggered, originTriggered \<rbrace> \<parallel>
      (foundTrig, originTrig) \<rbrakk>
    InputBuffers"

definition move_OperationMapping :: "('ch, 'st) action" where
  "move_OperationMapping = \<mu> (\<lambda> X.
    moveCall\<^bold>?lv \<rightarrow> setVel\<^bold>!(real lv *\<^sub>3 oriToVec ori) \<rightarrow> X
     \<box>
    proceed \<rightarrow> X)"

definition turnBack_OperationMapping :: "('ch, 'st) action" where
  "turnBack_OperationMapping = \<mu> (\<lambda> X.
    turnBackCall
      \<rightarrow> setVel\<^bold>!(0, 0, 0) 
      \<rightarrow> setAngVel\<^bold>!(pi, 0, 0)
      \<rightarrow> (tock
      \<rightarrow> setAngVel\<^bold>!(0, 0, 0)
      \<rightarrow> X)
     \<box>
    proceed \<rightarrow> X)"

definition takeoff_OutputEventMapping :: "('ch, 'st) action" where
  "takeoff_OutputEventMapping = \<mu> (\<lambda> X.
    takeoff\<^bold>.Out \<rightarrow> setVel\<^bold>!(0, 0, 1) \<rightarrow> X
     \<box>
    (proceed \<rightarrow> X))"

definition land_OutputEventMapping :: "('ch, 'st) action" where
  "land_OutputEventMapping = \<mu> (\<lambda> X.
    land\<^bold>.Out \<rightarrow> setVel\<^bold>!(0, 0, -1) \<rightarrow> X
     \<box>
    (proceed \<rightarrow> X))"

definition Mapping :: "('ch, 'st) action" where
  "Mapping =
    move_OperationMapping
      \<lbrakk> \<^bold>0 \<parallel> \<^bold>0 \<rbrakk>
    (turnBack_OperationMapping
      \<lbrakk> \<^bold>0 \<parallel> \<^bold>0 \<rbrakk>
    (takeoff_OutputEventMapping
      \<lbrakk> \<^bold>0 \<parallel> \<^bold>0 \<rbrakk>
    land_OutputEventMapping))"


definition RescueRoboWorld :: "('ch, 'st) action" where
  "RescueRoboWorld = Environment \<lbrakk> \<^bold>v \<parallel> \<lbrace> setVel, setAngVel, proceed \<rbrace> \<parallel> \<^bold>0 \<rbrakk> Mapping"

end


section \<open>Test Generation Algorithm\<close>

dataspace rescueDrone = rescueDroneRoboChart + rescueDroneRoboWorld +

context rescueDrone
begin


method rct_refine = (simp?, unfold rct_defs, rule ref_preorder.order_refl)
method rct_refine_by_trace = fail
method rct_simp_counterexample = clarsimp

ML \<open>fun obtainCounterexample ctxt goal = (SOME [
    @{term "prism_build takeoff Out"},
    @{term "prism_build tock ()"},
    @{term "prism_build tock ()"}
  ], ctxt)\<close>

ML \<open>fun term_to_name ctxt term =
      let val text = XML.content_of (YXML.parse_body (Syntax.string_of_term ctxt term))
          val ident_tokens = String.tokens (not o Symbol.is_letdig o str) text
      in if Symbol_Pos.is_identifier text then text else (hd ident_tokens) ^ "_" ^ (SHA1.rep (SHA1.digest text))
      end\<close>
          
ML \<open>fun checkRefinement ctxt (spec : term) (impl : term) =
      let val spec_type = Term.fastype_of spec
          val ref_by = Logic.varify_global @{term ref_by}
          val ref_by_type = Term.fastype_of ref_by
          val insts = Sign.typ_match @{theory} (#1 (Term.dest_funT ref_by_type), spec_type) Vartab.empty
          val ref_by_inst = Envir.subst_term_types insts ref_by
          val statement = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (ref_by_inst $ spec $ impl))
          val goal = Goal.init  statement
          val rct_refine = Method.method ctxt (Token.make_src (@{method rct_refine}, Position.start) [])
          val goal_seq = rct_refine ctxt [] (ctxt, goal)
      in case Seq.pull goal_seq of
            NONE => (* proof method failed, try to construct counterexample *) obtainCounterexample ctxt goal |>> SOME
          | SOME (Seq.Result (ctxt, goal), _) => (* proof method succeeded, do we have a finished goal? *)
              if Thm.no_prems goal then
                (* This looks like a finished goal, convert it to a finished theorem and save it *)
                let val finished_goal = Goal.finish ctxt goal
                    val impl_ident = term_to_name ctxt impl
                    val spec_ident = term_to_name ctxt spec
                    val name = impl_ident ^ "_refines_" ^ spec_ident
                    val binding = Binding.name name
                    val ((bound_name, _), ctxt) = Local_Theory.note ((binding, []), [finished_goal]) ctxt
                in (NONE, ctxt) end
              else (* proof method didn't finish the proof, try to construct counterexample *) (NONE, ctxt)
          | SOME (Seq.Error err, _) => let val _ = warning (err ()) in obtainCounterexample ctxt goal |>> SOME end
      end
\<close>

ML \<open>fun checkTraceOf ctxt (impl : term) (trace : term list)  = (NONE, ctxt)\<close>

end

ML \<open>fun traceToProcess typ (trace : term list) =
          if null trace then
            Const (@{const_name Skip}, typ)
          else 
            Const (@{const_name csync}, typ --> typ --> typ) $ (hd trace) $ traceToProcess typ (tl trace)\<close>

ML \<open>structure TraceSet = Set(type key = term list val ord = list_ord Term_Ord.fast_term_ord)\<close>
ML \<open>structure TermSet = Set(type key = term val ord = Term_Ord.fast_term_ord)\<close>

ML \<open>fun testGeneration ctxt rct muts rwd n = 
      let val rctType = fastype_of rct
          fun testGenLoop ctxt mutsToCheck refiningMuts failedMuts feasibleTrs infeasibleTrs n =
            let val tracesThenAny =
                      map (fn trace => Const (@{const_name cseq}, rctType --> rctType --> rctType) $ traceToProcess rctType trace $
                        Const (@{const_abbrev Chaos}, rctType)) (TraceSet.dest (infeasibleTrs))
                val infeasibleProcess = Const (@{const_name Sup}, (HOLogic.mk_setT rctType) --> rctType) $ (HOLogic.mk_set rctType tracesThenAny)
                val robochartPlusTraces = 
                  if null tracesThenAny then
                    rct
                  else
                    Const (@{const_name "sup"}, rctType --> rctType --> rctType) $ rct $ infeasibleProcess
                fun checkMutant mut (refMuts, failMuts, traces, ctxt) = 
                  case checkRefinement ctxt robochartPlusTraces mut of
                      (NONE, ctxt) => (
                        (*writeln ("refining mutant: " ^ (Syntax.string_of_term ctxt mut));*)
                        (TermSet.insert mut refMuts, failedMuts, traces, ctxt))
                    | (SOME NONE, ctxt) => (
                        (*writeln ("failed mutant: " ^ (Syntax.string_of_term ctxt mut));*)
                        (refMuts, TermSet.insert mut failedMuts, traces, ctxt))
                    | (SOME (SOME trace), ctxt) => (
                        (*writeln ("trace generated: " ^ (String.concatWith " \<rightarrow> " (map (Pretty.pure_string_of o Syntax.pretty_term ctxt) trace)));*)
                        (refMuts, failedMuts, TraceSet.insert trace traces, ctxt))
                val (refMuts, failMuts, traces, ctxt) =
                      TermSet.fold checkMutant mutsToCheck (refiningMuts, failedMuts, TraceSet.empty, ctxt)
                fun checkTrace trace (fts, its, ctxt) =
                  case checkTraceOf ctxt rwd trace of
                      (NONE, ctxt) => (
                        (*writeln ("feasible trace: " ^ (String.concatWith " \<rightarrow> " (map (Pretty.pure_string_of o Syntax.pretty_term ctxt) trace)));*)
                        (TraceSet.insert trace fts, its, ctxt))
                    | (SOME counterexamplePrefix, ctxt) => (
                        (*writeln ("infeasible trace counterexample: " ^ (String.concatWith " \<rightarrow> " (map (Pretty.pure_string_of o Syntax.pretty_term ctxt) counterexamplePrefix)));*)
                        (fts, TraceSet.insert counterexamplePrefix its, ctxt))
                val (fts, its, ctxt) = TraceSet.fold checkTrace traces (feasibleTrs, infeasibleTrs, ctxt)
                val newMutsToCheck = TermSet.subtract failMuts (TermSet.subtract refMuts mutsToCheck)
            in if n > 1 then testGenLoop ctxt newMutsToCheck refMuts failMuts fts its (n-1) else (refMuts, failMuts, fts, its, ctxt)
            end
          val (refMuts, failMuts, fts, its, ctxt) =
            testGenLoop ctxt (TermSet.make muts) TermSet.empty TermSet.empty TraceSet.empty TraceSet.empty n
          val term_string = Pretty.pure_string_of o Syntax.pretty_term ctxt
          fun traceToString trace = String.concatWith " \<rightarrow> " (map term_string trace)
      in
        writeln "Feasible Traces Generated:";
        map (fn trace => (writeln ("  " ^ (traceToString trace)))) (TraceSet.dest fts);
        writeln "Refining mutants:";
        map (fn t => (writeln ("  " ^ (term_string t)))) (TermSet.dest refMuts);
        ctxt
      end\<close>

subsection \<open>Testing the Test Generation Algorithm\<close>

context rescueDrone
begin

lemma "RescueDrone \<sqinter> \<Sqinter> {} \<sqsubseteq> RescueDrone_mTransTarget_Output1"
  by (simp, rct_refine)

context
  defines "DELIVERY \<equiv> 2"
  defines "LV \<equiv> 1"
  defines "TOP \<equiv> 1"
  defines "TURN \<equiv> 1"
begin


ML \<open>val RescueDroneMutants = [
    @{term RescueDrone_mTransTarget_Output0},
    @{term RescueDrone_mTransTarget_Output1},
    @{term RescueDrone_mTransTarget_Output2},
    @{term RescueDrone_mTransTarget_Output3},
    @{term RescueDrone_mTransTarget_Output4},
    @{term RescueDrone_mTransTarget_Output5},
    @{term RescueDrone_mTransTarget_Output6},
    @{term RescueDrone_mTransTarget_Output7},
    @{term RescueDrone_mTransTarget_Output8},
    @{term RescueDrone_mTransTarget_Output9}
  ]\<close>

ML \<open>Outer_Syntax.local_theory \<^command_keyword>\<open>generate_tests_rct\<close>
  "generates tests from the semantics of a RoboChart model and its mutants, incorporating a RoboWorld model"
  ((((Parse.$$$ "RoboChart" -- Parse.$$$ "=")  |-- Parse.term)
    -- ((Parse.$$$ "Mutants" -- Parse.$$$ "=")  |-- Parse.list1 Parse.term)
    -- ((Parse.$$$ "RoboWorld" -- Parse.$$$ "=")  |-- Parse.term)
    -- ((Parse.$$$ "Iterations" -- Parse.$$$ "=")  |-- Parse.nat))
  >> (fn (((rct, muts), rwd), n) => fn ctxt =>
      let val rct_term = Syntax.read_term ctxt rct
          val mut_terms = map (Syntax.read_term ctxt) muts
          val rwd_term = Syntax.read_term ctxt rwd
      in testGeneration ctxt rct_term mut_terms rwd_term n
      end))\<close>

generate_tests_rct
  RoboChart = "RescueDrone"
  Mutants =
    "RescueDrone_mTransTarget_Output0",
    "RescueDrone_mTransTarget_Output1",
    "RescueDrone_mTransTarget_Output2",
    "RescueDrone_mTransTarget_Output3",
    "RescueDrone_mTransTarget_Output4",
    "RescueDrone_mTransTarget_Output5",
    "RescueDrone_mTransTarget_Output6",
    "RescueDrone_mTransTarget_Output7",
    "RescueDrone_mTransTarget_Output8",
    "RescueDrone_mTransTarget_Output9"
  RoboWorld = "RescueRoboWorld"
  Iterations = 1

print_theorems
