theory TestGen
  imports IsaCircus
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


definition RoboWorld :: "('ch, 'st) action" where
  "RoboWorld = Environment \<lbrakk> \<^bold>v \<parallel> \<lbrace> setVel, setAngVel, proceed \<rbrace> \<parallel> \<^bold>0 \<rbrakk> Mapping"

end


dataspace rescueDrone = rescueDroneRoboChart + rescueDroneRoboWorld +

context rescueDrone
begin

term "rescueDrone"
typ "'a \<Longrightarrow>\<^sub>\<triangle> 'b"
ML_val \<open>[
    @{term "prism_build takeoff Out"},
    @{term "prism_build tock ()"},
    @{term "prism_build tock ()"}
  ]\<close>

ML \<open>fun checkRefinement (spec : term) (impl : term) =
      case Term.head_of impl of
        (* Output0 - Expected counterexample: takeoff\<^bold>.Out, tock, tock *)
        Const ("TestGen.rescueDroneRoboChart.RescueDrone_mTransTarget_Output0",_) =>
          SOME [
            @{term "prism_build takeoff Out"},
            @{term "prism_build tock ()"},
            @{term "prism_build tock ()"}
          ]
        (* Output1 - Refines original *)
      | Const ("TestGen.rescueDroneRoboChart.RescueDrone_mTransTarget_Output1",_) => NONE
        (* Output2 - Expected counterexample: takeoff\<^bold>.Out, tock, takeoff\<^bold>.Out *)
      | Const ("TestGen.rescueDroneRoboChart.RescueDrone_mTransTarget_Output2",_) =>
          SOME [
            @{term "prism_build takeoff Out"},
            @{term "prism_build takeoff Out"}
          ]
        (* Output3 - Expected counterexample: takeoff\<^bold>.Out, tock, moveCall\<^bold>.LV, found\<^bold>.In, land\<^bold>.Out,
            tock, tock, takeoff\<^bold>.Out, tock, turnBackCall, tock, moveCall\<^bold>.LV, tock, tock, takeoff\<^bold>.Out *)
      | Const ("TestGen.rescueDroneRoboChart.RescueDrone_mTransTarget_Output3",_) =>
          SOME [
            @{term "prism_build takeoff Out"},
            @{term "prism_build tock ()"},
            @{term "prism_build moveCall LV"},
            @{term "prism_build found In"},
            @{term "prism_build land Out"},
            @{term "prism_build tock ()"},
            @{term "prism_build tock ()"},
            @{term "prism_build takeoff Out"},
            @{term "prism_build tock ()"},
            @{term "prism_build turnBackCall ()"},
            @{term "prism_build tock ()"},
            @{term "prism_build moveCall LV"},
            @{term "prism_build tock ()"},
            @{term "prism_build tock ()"},
            @{term "prism_build takeoff Out"}
          ]
        (* Output4 - Refines original *)
      | Const ("TestGen.rescueDroneRoboChart.RescueDrone_mTransTarget_Output4",_) => NONE
        (* Output5 - Expected counterexample: takeoff\<^bold>.Out, tock, origin\<^bold>.In *)
      | Const ("TestGen.rescueDroneRoboChart.RescueDrone_mTransTarget_Output5",_) =>
          SOME [
            @{term "prism_build takeoff Out"},
            @{term "prism_build tock ()"},
            @{term "prism_build origin In"}
          ]
        (* Output6 - Expected counterexample: takeoff\<^bold>.Out, tock, tock, tock, takeoff\<^bold>.Out *)
      | Const ("TestGen.rescueDroneRoboChart.RescueDrone_mTransTarget_Output6",_) =>
          SOME [
            @{term "prism_build takeoff Out"},
            @{term "prism_build tock ()"},
            @{term "prism_build tock ()"},
            @{term "prism_build tock ()"},
            @{term "prism_build takeoff Out"}
          ]
        (* Output7 - Refines original *)
      | Const ("TestGen.rescueDroneRoboChart.RescueDrone_mTransTarget_Output7",_) => NONE
        (* Output8 - Expected counterexample: origin\<^bold>.In *)
      | Const ("TestGen.rescueDroneRoboChart.RescueDrone_mTransTarget_Output8",_) =>
          SOME [
            @{term "prism_build origin In"}
          ]
        (* Output9 - Expected counterexample: takeoff\<^bold>.Out, tock, moveCall\<^bold>.LV, found\<^bold>.In, land\<^bold>.Out,
            tock, tock, takeoff\<^bold>.Out, tock, turnBackCall, tock, moveCall\<^bold>.LV, origin\<^bold>.In, turnBackCall,
            tock, land\<^bold>.Out, moveCall\<^bold>.LV *)
      | Const ("TestGen.rescueDroneRoboChart.RescueDrone_mTransTarget_Output9",_) =>
          SOME [
            @{term "prism_build takeoff Out"},
            @{term "prism_build tock ()"},
            @{term "prism_build moveCall LV"},
            @{term "prism_build found In"},
            @{term "prism_build land Out"},
            @{term "prism_build tock ()"},
            @{term "prism_build tock ()"},
            @{term "prism_build takeoff Out"},
            @{term "prism_build tock ()"},
            @{term "prism_build turnBackCall ()"},
            @{term "prism_build tock ()"},
            @{term "prism_build moveCall LV"},
            @{term "prism_build Origin In"},
            @{term "prism_build turnBackCall ()"},
            @{term "prism_build tock ()"},
            @{term "prism_build land Out"},
            @{term "prism_build moveCall LV"}
          ]
      | _ => SOME []\<close>
ML \<open>Option.map\<close>
ML \<open>fun checkTraceOf (impl : term) (trace : term list)  =
          let fun event_of (Const ("Prisms.prism.prism_build", _) $ Free (name, _) $ _) = name
              fun check_trace (x :: xs) =
                  if x = @{term "moveCall"} then if hd xs = @{term "found"} then SOME [x, hd xs] else NONE else NONE
          in check_trace trace end\<close>

end

ML \<open>fun traceToProcess (trace : term list) =
          if null trace then
            @{term Skip}
          else 
            @{term csync} $ (hd trace) $ traceToProcess (tl trace)\<close>


ML \<open>structure TraceSet = Set(type key = term list val ord = list_ord Term_Ord.fast_term_ord)\<close>

ML \<open>fun testGeneration rct muts rwd n = 
      let val rctType = fastype_of rct
          val feasibleTraces = Unsynchronized.ref TraceSet.empty
          val infeasibleTraces = Unsynchronized.ref TraceSet.empty
      in while TraceSet.size (!feasibleTraces) < n do (
        let val tracesThenAny =
                  map (fn trace => @{term "cseq"} $ traceToProcess trace $
                    @{term Chaos}) (TraceSet.dest (!infeasibleTraces))
            val infeasibleProcess = @{term Sup} $ (HOLogic.mk_set rctType tracesThenAny)
            val robochartPlusTraces = @{term "(\<sqinter>)"} $ rct $ infeasibleProcess
            val testTraces =
                  map_filter (fn mutant => checkRefinement robochartPlusTraces mutant) muts
            val checkTrace = fn trace => 
                  case checkTraceOf rwd trace of
                      NONE => (SOME trace, NONE)
                    | SOME counterexamplePrefix => (NONE, SOME counterexamplePrefix)
            val (fts, its) =
                  apply2 (TraceSet.make o (map_filter I)) (map_split checkTrace testTraces)
        in
          feasibleTraces := TraceSet.merge (!feasibleTraces, fts);
          infeasibleTraces := TraceSet.merge (!infeasibleTraces, its)
        end
      ); TraceSet.dest (!feasibleTraces)
      end\<close>

(* writeln ( (String.concatWith ", \n" (map (fn s => "[" ^ String.concatWith ", " (map (Syntax.string_of_term @{context}) s) ^ "]") (TraceSet.dest (!feasibleTraces)))) ) *)

context rescueDrone
begin

context
  defines "DELIVERY \<equiv> 2"
  defines "LV \<equiv> 1"
  defines "TOP \<equiv> 1"
  defines "TURN \<equiv> 1"
begin

term RescueDrone_mTransTarget_Output0

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

ML_val \<open>let val rct = @{term RescueDrone}
            val muts = RescueDroneMutants
            val rwd = @{term RoboWorld}
            val n = 1
            val rctType = fastype_of rct
            val feasibleTraces = Unsynchronized.ref []
            val infeasibleTraces = Unsynchronized.ref []
            val tracesThenAny = map (fn trace => @{term "cseq"} $ traceToProcess trace $ @{term Chaos}) (!infeasibleTraces)
            val infeasibleProcess = @{term Sup} $ (HOLogic.mk_set rctType tracesThenAny)
        in infeasibleProcess end\<close>

ML \<open>testGeneration\<close>
ML_val \<open>testGeneration @{term RescueDrone} RescueDroneMutants @{term RoboWorld} 1\<close>
