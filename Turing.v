
From LF Require Import Logic.
From LF Require Import Poly.
From Coq Require Import Strings.String.

Module Turing.

(* Final states of Turing machines *)
Inductive State := 
  | Accept | Reject | Loop.

(* Turing machines *)
Definition TM_t := string -> State.

Definition accepts (M:TM_t) (w:string) := M w = Accept.
Definition rejects (M:TM_t) (w:string) := M w = Reject.
Definition halts_on (M:TM_t) (w:string) := accepts M w \/ rejects M w.
Definition loops_on (M:TM_t) (w:string) := M w = Loop.

(* Formal contents of a machine's input string *)
Inductive Input := 
  | instr (w:string)
  | inmach (M:TM_t)
  | inms (M:TM_t) (w:string)
  | inmm (M1 M2:TM_t).
  
(* Abstract encoding/decoding functions *)
Variable encode : Input -> string.
Variable decode : string -> Input.
(* Assume that the encoding works well *)
Axiom encode_bijective : 
  forall (i:Input), decode (encode i) = i.

(* ########################################################################## *)

(* The Acceptance Problem of Turing machines (ATM) is undecidable. *)

Definition decides_ATM (D:TM_t) :=
  forall (M:TM_t) (w:string),
    (accepts M w -> accepts D (encode (inms M w)))
    /\ (~accepts M w -> rejects D (encode (inms M w))).

Theorem ATM_undecidable: 
  ~ exists DATM:TM_t, decides_ATM DATM.
Proof.
  unfold decides_ATM.
  unfold not; intros H; 
  (* Suppose a decider DATM exists for ATM:
     If its input string x encodes a machine M and another string w, 
     DATM accept x exactly if M accepts w, 
     else rejects x (even if M loops on w). *)
  destruct H as [DATM H].
  (* Mreb - "rebel" machine
     If the input string x is a encoding <M> of a single TM M, 
     feed <M,<M>> (an encoding of [M together with a copy of x]) 
     to DATM, and do exactly the opposite as DATM does *)
  remember 
    ( 
      fun x:string =>
        match (decode x) with 
        | inmach M => 
          match (DATM (encode (inms M x))) with 
          | Accept => Reject
          | _ => Accept
          end
        | _ => Reject
      end
    ) 
  as Mreb eqn:Progreb.
  (* What happens when Mreb tries to decide its own encoding?
     reb_str - Mreb's string encoding, <Mreb>
     S_reb_self - The final state of Mreb when 
       invoked on its own encoding *)
  remember (encode (inmach Mreb)) as reb_str eqn:Erebs.
  remember (Mreb reb_str) as S_reb_self eqn:Erebself.
  (* Make a copy, since we want to keep track of the identity
     while using another instance to simulate the semantics of DATM *)
  remember Erebself as Erebself' eqn:EEself. clear EEself.
  rewrite Progreb in Erebself'.
  rewrite Erebs in Erebself'.
  assert (Id_inreb : decode (encode (inmach Mreb)) = (inmach Mreb)).
    { apply encode_bijective. }
  rewrite Id_inreb in Erebself'.
  rewrite <- Erebs in Erebself'.
  specialize H with Mreb reb_str.
  destruct (S_reb_self).
  + (* Mreb "accepts" reb_str *)
    assert (Hacc : accepts Mreb reb_str). { unfold accepts. congruence. }
    (* DATM accepts <Mreb, reb_str> *)
    destruct H as [H _]; apply H in Hacc.
    (* Mreb proceeds to reject reb_str *)
    rewrite Hacc in Erebself'. 
    inversion Erebself'.
  + (* Mreb "rejects" reb_str *)
    assert (Hnacc: ~accepts Mreb reb_str). 
      { 
        unfold accepts. unfold not; intros. 
        rewrite H0 in Erebself. discriminate. 
      } 
    (* DATM rejects <Mreb, reb_str>  *)
    destruct H as [_ H]; apply H in Hnacc.
    (* Mreb proceeds to accept reb_str *)
    rewrite Hnacc in Erebself'. inversion Erebself'.
  + (* Mreb "loops on" reb_str 
        - bogus case since Mreb is a decider *)
    assert (Hnacc: ~accepts Mreb reb_str). 
      { 
        unfold accepts. unfold not; intros. 
        rewrite H0 in Erebself. discriminate. 
      } 
    destruct H as [_ H]; apply H in Hnacc.
    rewrite Hnacc in Erebself'. inversion Erebself'.
Qed.

(* ########################################################################## *)

(* The Halting Problem of Turing machines (HALT) is undecidable. *)

Definition decides_HALT (D:TM_t) := 
  forall (M:TM_t) (w:string),
    (halts_on M w -> accepts D (encode (inms M w)))
    /\ (loops_on M w -> rejects D (encode (inms M w))).

Theorem HALT_undecidable : 
  ~ exists DHALT:TM_t, decides_HALT DHALT.
Proof. 
  unfold decides_HALT, not; intros H; destruct H as [DHALT H]. 
  (* Assume that a decider DHALT exists for HALT,
     we can then paradoxically decide ATM. *)
  (* MAaux - a helper for deciding ATM
     If M accepts on w, MAux halts on <M,w>;
     else, MAux loops on <M,w> *)
  remember 
    (
      fun x:string =>
        match (decode x) with 
        | inms M w => 
          match (M w) with 
          | Accept => Accept
          | Reject => Loop
          | Loop => Loop
          end
        | _ => Reject
      end
    )
  as MAaux eqn:Progaux.
  (* DATM - a decider for ATM
     Let DHALT decide <MAaux,<M,w>>. 
     
     If M accepts w, 
       then MAaux halts on <M,w>, 
       DHALT accepts <MAaux,<M,w>>, 
       DATM accepts <M,w>;
     
     If M does not accept w, 
       then MAux loops, 
       DHALT rejects, 
       DATM rejects. *)
  remember 
    (
      fun x:string =>
        match (decode x) with 
        | inms M w => 
          match DHALT (encode (inms MAaux x)) with 
          | Accept => Accept 
          | _ => Reject
          end
        | _ => Reject
      end
    ) as DATM eqn:ProgDA.
  (* Show that if DHALT decides HALT, then DATM decides ATM, 
     contradicting ATM_undecidable. *)
  assert (HDA : decides_ATM DATM).
    {
      unfold decides_ATM. intros.
      remember (encode (inms M w)) as Mw eqn:EMw. (* <M,w> *)
      remember (encode (inms MAaux Mw)) as AuxMw eqn:EAuxMw. (* <MAaux,<M,w>> *)
      split; intros. 
      + (* M accepts w *)
        remember (MAaux Mw) as Saux eqn:ESaux. (* Final state of MAaux on <M,w> *)
        remember ESaux as ESaux' eqn:_E; clear _E.
        rewrite Progaux in ESaux.
        assert (Id_Mw : decode Mw = inms M w).
          { rewrite EMw. apply encode_bijective. }
        rewrite Id_Mw in ESaux.
        unfold accepts in H0. rewrite H0 in ESaux. (* MAaux accepts <M,w> *)
        
        (* DHALT is abstract, so there is no [remember (DHALT AuxMw)] *)
        specialize H with MAaux Mw; destruct H as [H _].
        assert (H_aux_hlt : halts_on MAaux Mw).
          { unfold halts_on. left. unfold accepts. congruence. }
        apply H in H_aux_hlt. (* DHALT accepts <MAaux,<M,w>> *)
        
        remember (DATM Mw) as SDA eqn:ESDA. (* Final state of DATM on <M,w> *)
        remember ESDA as ESDA' eqn:_E; clear _E.
        rewrite ProgDA in ESDA.
        rewrite Id_Mw in ESDA.
        rewrite H_aux_hlt in ESDA.
        unfold accepts. congruence. (* DATM accepts <M,w> *)
      + (* M does not accept w *)
        remember (MAaux Mw) as Saux eqn:ESaux. (* Final state of MAaux on <M,w> *)
        remember ESaux as ESaux' eqn:_E; clear _E.
        rewrite Progaux in ESaux.
        assert (Id_Mw : decode Mw = inms M w).
          { rewrite EMw. apply encode_bijective. }
        rewrite Id_Mw in ESaux.
        unfold accepts in H0.
        destruct (M w) eqn:ESM. (* Final state of M on w *)
        - (* M accepts w - bogus case *)
          assert (A : Accept = Accept). { reflexivity. } contradiction.
          
        - (* M rejects w 
             MAaux loops on <M,w> *)
          specialize H with MAaux Mw; destruct H as [_ H].
          unfold loops_on in H. rewrite ESaux' in ESaux. apply H in ESaux.
          unfold rejects in ESaux. (* DHALT rejects <MAux,<M,w>> *)
          
          remember (DATM Mw) as SDA eqn:ESDA. remember ESDA as ESDA' eqn:_E; clear _E. 
          rewrite ProgDA in ESDA. rewrite Id_Mw in ESDA. rewrite ESaux in ESDA.
          unfold rejects. congruence. (* DATM rejects <M,w> *)
          
        - (* M loops on w 
             MAaux loops on <M,w> *)
          specialize H with MAaux Mw; destruct H as [_ H].
          unfold loops_on in H. rewrite ESaux' in ESaux. apply H in ESaux.
          unfold rejects in ESaux. (* DHALT rejects <MAux,<M,w>> *)
          
          remember (DATM Mw) as SDA eqn:ESDA. remember ESDA as ESDA' eqn:_E; clear _E. 
          rewrite ProgDA in ESDA. rewrite Id_Mw in ESDA. rewrite ESaux in ESDA.
          unfold rejects. congruence.  (* DATM rejects <M,w> *)
    }
  remember ATM_undecidable as AU. destruct AU.
  exists DATM. assumption.
Qed.

(* ########################################################################## *)

(* A machine has an empty language 
   exactly if it accepts no input at all. *)
Definition empty_lang (M:TM_t) : Prop :=
  forall (x:string), ~ accepts M x.

(* The Empty Language problem of Turing machines (ETM) is undecidable. *)

Definition decides_ETM (D:TM_t) := 
  forall (M:TM_t),
    (empty_lang M -> accepts D (encode (inmach M))) 
    /\ (~ empty_lang M -> rejects D (encode (inmach M))).

Theorem ETM_undecidable: 
  ~ exists DETM:TM_t, decides_ETM DETM.
Proof. 
  (* Assume there exists a decider DETM for ETM: 
     given <M>, it accepts if <M> has an empty language and rejects otherwise *)
  unfold decides_ETM, not; intros H; destruct H as [DETM H].
  (* The higher-order template for a helper machine - 
     For any fixed (M, w), the "bespoke" helper specialized with M, w 
     imitates the final state of M on w for its own final state on free input s.
     It has an empty language exactly if M does not accept w.
  *) 
  remember 
    (fun (M:TM_t) (w:string) (s:string) => (M w))
    as aux_tmpl eqn:Progtempl.
  (* DATM - a decider for ATM
     Given <M,w>, it creates the helper machine MAaux specialized with (M, w)
     and asks DETM whether MAaux has an empty language.
     If M accepts w, then DETM rejects <MAaux>, and DATM rejects <M,w>;
     If M does not accept w, then DETM accepts <MAaux>, and DATM accepts <M,w>. *)
  remember 
    (
      fun x:string => 
        match (decode x) with 
        | inms M w => 
          match (DETM (encode (inmach (aux_tmpl M w)))) with 
          | Accept => Reject
          | Reject => Accept 
          | _ => Reject (* bogus *)
          end
        | _ => Reject
        end
    )
  as DATM eqn:ProgDA.
  (* Show that if DETM decides ETM, then DATM decides ATM - contradiction. *)
  assert (HDA : decides_ATM DATM).
    {
      unfold decides_ATM. intros. 
      remember (M w) as SM eqn:ESM. (* Final state of M on w *)
      remember (encode (inms M w)) as Mw eqn:EMw. (* <M,w> *)
      remember (aux_tmpl M w) as MAaux eqn:Progaux. (* Helper machine specialized with (M, w) *)
      assert (Id_Mw : decode Mw = (inms M w)).
        { rewrite EMw. apply encode_bijective. }
      split; intros. 
      + (* M accepts w,
           MAaux has a non-empty language *)
        assert (Haux_nempty : ~ empty_lang MAaux).
          {
            unfold not; intros. unfold empty_lang in H1.
            remember (MAaux w) as Saux eqn:ESaux.
            remember ESaux as ESaux' eqn:_E; clear _E.
            (* M accepts w, and MAaux running on w accepts accordingly *)
            rewrite Progaux, Progtempl in ESaux. 
            unfold accepts in H0. rewrite H0 in ESaux. rewrite ESaux in ESaux'.
            specialize H1 with w. unfold accepts in H1. 
            symmetry in ESaux'. contradiction.
          }
        remember (DATM Mw) as SDA eqn:ESDA. (* Final state of DATM on <M,w> *)
        remember ESDA as ESDA' eqn:_E; clear _E.
        rewrite ProgDA in ESDA.
        rewrite Id_Mw in ESDA.
        specialize H with MAaux; destruct H as [_ H].
        (* DETM rejects <MAaux> *)
        apply H in Haux_nempty. unfold rejects in Haux_nempty. 
        rewrite <- Progaux in ESDA. rewrite Haux_nempty in ESDA. 
        unfold accepts. congruence. (* DATM accepts <M,w> *)
      + (* M does not accept w,
           MAaux has an empty language *)
        assert (Haux_empty : empty_lang MAaux).
          {
            unfold accepts in H0.
            destruct SM.
            + (* M accepts w - bogus *)
              symmetry in ESM. contradiction.
            + (* M rejects w *)
              unfold empty_lang. intros s. 
              remember (MAaux s) as Saux eqn:ESaux.
              remember ESaux as ESaux' eqn:_E; clear _E.
              rewrite Progaux, Progtempl in ESaux'.
              unfold accepts. congruence.
            + (* M loops on w *)
              unfold empty_lang. intros s. 
              remember (MAaux s) as Saux eqn:ESaux.
              remember ESaux as ESaux' eqn:_E; clear _E.
              rewrite Progaux, Progtempl in ESaux'.
              unfold accepts. congruence.
          }
        specialize H with MAaux; destruct H as [H _].
        apply H in Haux_empty. (* DETM accepts <MAaux> *)
        unfold accepts in Haux_empty.
        remember (DATM Mw) as SDA eqn:ESDA.
        remember ESDA as ESDA' eqn:_E; clear _E.
        rewrite ProgDA in ESDA.
        rewrite Id_Mw in ESDA.
        rewrite <- Progaux in ESDA.
        rewrite Haux_empty in ESDA. (* DATM rejects <M,w> *)
        unfold rejects. congruence.
    }
  remember ATM_undecidable as AU.
  unfold not in AU; destruct AU.
  exists DATM. assumption.
Qed.

(* ########################################################################## *)

(* Two machines are equivalent exactly if they 
    have the same language, that is, 
    they accept the very same strings. *)
Definition same_lang (M1 M2:TM_t) := 
  forall x:string,
    accepts M1 x <-> accepts M2 x.

(* The Equivalence Problem of Turing machines (EQTM) is undecidable. *)

Definition decides_EQTM (D:TM_t) := 
  forall (M1 M2:TM_t),
    (same_lang M1 M2 -> accepts D (encode (inmm M1 M2)))
    /\ (~ same_lang M1 M2 -> rejects D (encode (inmm M1 M2))).

Theorem EQTM_undecidable : 
  ~ exists DEQ:TM_t, decides_EQTM DEQ.
Proof. 
  (* Suppose that a decider DEQ exists for EQTM:
     Given <M1,M2>, it accepts if M1, M2 have the same language
     and rejects otherwise. *)
  unfold decides_EQTM, not; intros H; destruct H as [DEQ H].
  (* If DEQ exists, then we could paradoxically decide ETM by 
     fixing an empty-language machine ME and testing for 
     equivalence against it with DEQ. *)
  remember ( fun x:string => Reject ) as ME eqn:ProgME. 
  assert (HME : empty_lang ME).
    {
      unfold empty_lang. intros. unfold accepts.
      remember (ME x) as SME eqn:ESME. 
      remember ESME as ESME' eqn:_E; clear _E.
      rewrite ProgME in ESME'. 
      unfold not; intros. congruence.
    }
  (* DETM - a hypothetical decider for ETM
     Given <M>, feeds <M,ME> into DEQ. 
     If DEQ accepts, then M, like ME, has an empty language; accept. 
     Else, reject. *)
  remember 
    (
      fun x:string => 
        match (decode x) with 
        | inmach M => 
          match (DEQ (encode (inmm M ME))) with 
          | Accept => Accept
          | Reject => Reject
          | _ => Reject (* Bogus *)
          end
        | _ => Reject
        end
    )
  as DETM eqn:ProgDE.
  assert (HDE : decides_ETM DETM).
    {
      unfold decides_ETM, not; intros.
      remember (encode (inmach M)) as Mstr eqn:EMs. (* <M> *)
      assert (Id_M : decode Mstr = inmach M).
        { rewrite EMs. apply encode_bijective. }
      split; intros. 
      + (* M has an empty language *)
        assert (HEQ : same_lang M ME).
          {
            unfold empty_lang in H0, HME.
            unfold same_lang; intros.
            split; intros. 
            - apply H0 in H1. inversion H1.
            - apply HME in H1; inversion H1.
          }
        specialize H with M ME; destruct H as [H _].
        apply H in HEQ.
        unfold accepts in HEQ.
        remember (DETM Mstr) as SDE eqn:ESDE. (* Final state of DETM on <M> *)
        remember ESDE as ESDE' eqn:_E; clear _E.
        rewrite ProgDE in ESDE'. rewrite Id_M in ESDE'.
        rewrite HEQ in ESDE'. 
        unfold accepts. congruence. (* DETM accepts <M> *)
      + (* M has a non-empty language *)
        assert (HnEQ : ~ same_lang M ME).
          {
            unfold empty_lang in H0, HME.
            unfold not; intros. unfold same_lang in H1.
            assert (Cd : forall x:string, ~ accepts M x).
              {
                intros x. specialize HME with x. specialize H1 with x.  
                unfold not; intros. apply H1 in H2. contradiction. 
              }
            contradiction.
          }
        specialize H with M ME; destruct H as [_ H].
        apply H in HnEQ. unfold rejects in HnEQ.
        remember (DETM Mstr) as SDE eqn:ESDE. (* Final state of DETM on <M> *)
        remember ESDE as ESDE' eqn:_E; clear _E.
        rewrite ProgDE in ESDE'. rewrite Id_M in ESDE'.
        rewrite HnEQ in ESDE'. 
        unfold rejects. congruence. (* DETM rejects <M> *)
    }
  remember ETM_undecidable as EU. 
  destruct EU. exists DETM. assumption.
Qed.

(* ########################################################################## *)

(* A property of Turing machines is nontrivial 
   if it holds of some but not all machines. 
   
   For later simplicity, it is additionally assumed that 
   such a property does not hold of machines with empty languages. 
 *)
Definition nontrivial (P:TM_t -> Prop) :=
  (exists M1:TM_t, P M1) 
  /\ (exists M2:TM_t, ~ P M2)
  /\ (forall M:TM_t, empty_lang M -> ~ P M).

(* A "property of languages" of Turing machines is one such that 
   if two machines have the same language, then they are in the 
   same relation to this property. *)
Definition prop_of_lang (P:TM_t -> Prop) :=
  forall (M1 M2:TM_t), 
    (same_lang M1 M2 -> (P M1 <-> P M2)).

Definition decides_property (D:TM_t) (P:TM_t -> Prop) := 
  forall M:TM_t,
    ((P M -> accepts D (encode (inmach M)))
     /\ (~ P M -> rejects D (encode (inmach M)))).

(* Rice's Theorem states that nontrivial properties of languages
   are undecidable. *)
   
Theorem Rice : 
  forall P:TM_t -> Prop, 
    (nontrivial P -> 
     prop_of_lang P -> 
     ~ exists D:TM_t, decides_property D P).
Proof. 
  (* Suppose that a decider DP exists for a nontrivial property of languages.
     We can then paradoxically decide ATM. *)
  intros P Hnt Hpl. unfold not; intros. 
  destruct H as [DP H].
  unfold nontrivial in Hnt. 
  destruct Hnt as [Hnt1 [Hnt2 Hnt3]].
  (* Since P holds of some machine M1,
     we specify a template for helper machines MAaux that, 
     when called from a decider for ATM and given fixed (M, w),
     - "loads" M1 whenever M accepts w, and
     - accepts nothing when M does not accept w. 
     Thus, if M accepts w, MAaux is equivalent to M1, and P holds;
     else it is an empty-language machine, and P does not hold. *)
  destruct Hnt1 as [M1 HM1].
  remember 
    (
      fun (M:TM_t) (w s:string) => 
        match (M w) with 
        | Accept => M1 s
        | _ => Loop
        end
    )
    as aux_tmpl eqn:Progtmpl.
  (* DATM - a hypothetical decider for ATM 
     Given <M,w>, it specializes a helper MAaux with (M, w)
     and lets the property decider DP decide <MAaux>.
     
     If M accepts w, 
       then P holds of MAaux, 
       DP accepts <MAux>,  
       DATM accepts <M,w>;
       
     If M does not accept w, 
       then P does not hold of MAaux,
       DP rejects <MAux>,  
       DATM rejects <M,w>. *)
  remember 
    (
      fun x:string => 
        match (decode x) with 
        | inms M w => 
          match (DP (encode (inmach (aux_tmpl M w)))) with 
          | Accept => Accept 
          | Reject => Reject
          | _ => Reject (* bogus *)
          end
        | _ => Reject
        end
    )
    as DATM eqn:ProgDA.
  assert (HDA : decides_ATM DATM).
    {
      unfold decides_ATM, not; intros. 
      remember (M w) as SM eqn:ESM. (* Final state of M on w *)
      remember (encode (inms M w)) as Mw eqn:EMw. (* <M,w> *)
      assert (Id_Mw : decode Mw = inms M w). 
        { rewrite EMw; apply encode_bijective; reflexivity. }
      remember (aux_tmpl M w) as MAaux eqn:Progaux. (* Helper *)
      remember Progaux as Progaux' eqn:_E; clear _E.
      unfold accepts, rejects. split; intros.
      + (* M accepts w,
           MAaux is equivalent to M1 *)
        rewrite Progtmpl in Progaux.
        assert (HauxEQ : same_lang MAaux M1).
          {
            unfold same_lang. intros. split; intros. 
            - (* MAaux accepts x -> M1 accepts x *)
              unfold accepts in H1. rewrite Progaux in H1. rewrite H0 in H1. 
              unfold accepts. assumption.
            - (* MAaux accepts x -> M1 accepts x *)
              unfold accepts in H1. 
              remember (MAaux x) as Saux eqn:ESaux. (* Final state of MAaux on x *)
              remember ESaux as ESaux' eqn:_E; clear _E.
              rewrite Progaux in ESaux'. rewrite H0 in ESaux'.
              unfold accepts; congruence.
          }
        unfold prop_of_lang in Hpl. specialize Hpl with MAaux M1. apply Hpl in HauxEQ.
        apply HauxEQ in HM1. 
        unfold decides_property in H. specialize H with MAaux. destruct H as [H _].
        apply H in HM1. unfold accepts in HM1.
        (* DP accepts <MAaux>, DATM accepts <M,w> *)
        rewrite ProgDA. rewrite Id_Mw. rewrite <- Progaux'. rewrite HM1. reflexivity. 
      + (* M does not accept w,
           MAux has empty language *)
        rewrite Progtmpl in Progaux'.
        assert (HauxE : empty_lang MAaux).
          {
            unfold empty_lang. intros. unfold not; intros. unfold accepts in H1.  
            destruct SM. 
            - (* M accepts w - bogus *)
              symmetry in ESM. contradiction. 
            - (* M rejects w *)
              rewrite Progaux' in H1. rewrite <- ESM in H1. inversion H1.
            - (* M loops on w *)
              rewrite Progaux' in H1. rewrite <- ESM in H1. discriminate. 
          }
        specialize Hnt3 with MAaux. apply Hnt3 in HauxE.
        unfold decides_property in H. specialize H with MAaux; destruct H as [_ H].
        apply H in HauxE. unfold rejects in HauxE.
        (* DP rejects <MAaux>, DATM rejects <M,w> *)
        rewrite ProgDA. rewrite Id_Mw. rewrite <- Progaux. rewrite HauxE. reflexivity. 
    }
  remember ATM_undecidable as AU. destruct AU; unfold not; intros. 
  exists DATM. assumption.
Qed.         

End Turing.

