open! Core
open! Hardcaml
open Hardcaml.Signal
open Hardcaml_waveterm

(* All our ranges are maximum 10 digits long.
   Idea:
  Use a BCD generator. The BCD generator would count up to 5 digits, and always start with 1.
  We get all our ranges simulatanously (there's < 40), and we duplicate the generated BCD
  value. If the duplicated value falls in any range, it's invalid, and we add it to the end
  result.
  For part 2, we duplicate up to 10 times, and we just filter out the BCD generator inputs
  that could be themselves be generated via duplication.
*)

module Bcd_counter = struct
  module I = struct
    type 'a t =
      { clock : 'a
      ; restart : 'a
      ; start_at : 'a [@bits 4]
      ; carry_in : 'a
      }
    [@@deriving hardcaml]
  end

  module O = struct
    type 'a t =
      { out : 'a [@bits 4]
      ; carry : 'a
      }
    [@@deriving hardcaml]
  end

  let create { I.clock; restart; start_at; carry_in } =
    let reg_spec = Reg_spec.create ~clock () in
    let out = Always.Variable.reg ~width:4 reg_spec in
    let next_out = Always.Variable.value out +: uresize ~width:4 carry_in in
    let overflow = next_out >=: of_int_trunc 10 ~width:4 in
    let next_out = mux2 overflow (zero 4) next_out in
    let carry = ~:restart &: overflow in
    let next_out = mux2 restart start_at next_out in
    Always.(compile [ out <-- next_out ]);
    { O.out = next_out; carry }
  ;;

  let test () =
    let module Test_circuit = Circuit.With_interface (I) (O) in
    let simulator =
      Cyclesim.create (Test_circuit.create_exn ~name:"bcd_counter" create)
    in
    let waves, sim = Waveform.create simulator in
    let restart = Cyclesim.in_port sim "restart" in
    let start_at = Cyclesim.in_port sim "start_at" in
    let carry_in = Cyclesim.in_port sim "carry_in" in
    start_at := Bits.of_int_trunc ~width:4 3;
    carry_in := Bits.one 1;
    restart := Bits.one 1;
    Cyclesim.cycle sim;
    restart := Bits.zero 1;
    for _ = 0 to 11 do
      Cyclesim.cycle sim
    done;
    restart := Bits.one 1;
    for _ = 0 to 4 do
      Cyclesim.cycle sim
    done;
    restart := Bits.zero 1;
    Cyclesim.cycle sim;
    Cyclesim.cycle sim;
    carry_in := Bits.zero 1;
    Cyclesim.cycle sim;
    Cyclesim.cycle sim;
    waves
  ;;

  let%expect_test _ =
    let waves = test () in
    Waveform.print
      ~wave_width:0
      ~display_rules:
        Display_rule.[ port_name_is "out" ~wave_format:Unsigned_int; Default ]
      waves;
    [%expect
      {|
      ┌Signals────────┐┌Waves──────────────────────────────────────────────┐
      │               ││──┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─┬─────────┬─┬─────       │
      │out            ││ 3│4│5│6│7│8│9│0│1│2│3│4│5│3        │4│5           │
      │               ││──┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─┴─────────┴─┴─────       │
      │carry_in       ││────────────────────────────────────────┐          │
      │               ││                                        └───       │
      │clock          ││┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌┐┌│
      │               ││ └┘└┘└┘└┘└┘└┘└┘└┘└┘└┘└┘└┘└┘└┘└┘└┘└┘└┘└┘└┘└┘└┘└┘└┘└┘│
      │restart        ││──┐                       ┌─────────┐              │
      │               ││  └───────────────────────┘         └───────       │
      │               ││────────────────────────────────────────────       │
      │start_at       ││ 3                                                 │
      │               ││────────────────────────────────────────────       │
      │carry          ││              ┌─┐                                  │
      │               ││──────────────┘ └───────────────────────────       │
      └───────────────┘└───────────────────────────────────────────────────┘
      |}]
  ;;
end

module Multidigit_bcd_counter = struct
  let num_digits = 5
  let num_bits = num_digits * 4

  module I = struct
    type 'a t =
      { start_at : 'a [@bits num_bits]
      ; restart : 'a
      ; clock : 'a
      }
    [@@deriving hardcaml]
  end

  module O = struct
    type 'a t =
      { out : 'a [@bits num_bits]
      ; num_digits_out : 'a [@bits 3]
      }
    [@@deriving hardcaml]
  end

  let create { I.start_at; restart; clock } =
    let out =
      List.range 0 num_digits
      |> List.folding_map ~init:vdd ~f:(fun carry_in i ->
        let start_at = start_at.:[(i * 4) + 3, i * 4] in
        let%tydi { out; carry } =
          Bcd_counter.create { Bcd_counter.I.clock; restart; start_at; carry_in }
        in
        carry, out)
    in
    let num_digits_out =
      List.fold
        ~init:(zero 3, 0)
        out
        ~f:(fun (result, digit_count) out ->
          let digit_count = digit_count + 1 in
          mux2 (out ==: zero 4) result (of_int_trunc ~width:3 digit_count), digit_count)
      |> fst
    in
    { O.out = concat_lsb out; num_digits_out }
  ;;

  let test ~start_bcd ~num_cycles =
    let module Test_circuit = Circuit.With_interface (I) (O) in
    let simulator =
      Cyclesim.create (Test_circuit.create_exn ~name:"bcd_counter" create)
    in
    let waves, sim = Waveform.create simulator in
    let start_at = Cyclesim.in_port sim "start_at" in
    let restart = Cyclesim.in_port sim "restart" in
    start_at := Bits.of_int_trunc ~width:num_bits start_bcd;
    restart := Bits.one 1;
    Cyclesim.cycle sim;
    restart := Bits.zero 1;
    for _ = 0 to num_cycles do
      Cyclesim.cycle sim
    done;
    waves
  ;;

  let%expect_test _ =
    let waves = test ~start_bcd:0x128 ~num_cycles:5 in
    Waveform.print ~wave_width:2 waves;
    [%expect
      {|
      ┌Signals────────┐┌Waves──────────────────────────────────────────────┐
      │clock          ││┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──│
      │               ││   └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  │
      │restart        ││──────┐                                            │
      │               ││      └───────────────────────────────────         │
      │               ││──────────────────────────────────────────         │
      │start_at       ││ 00128                                             │
      │               ││──────────────────────────────────────────         │
      │               ││──────────────────────────────────────────         │
      │num_digits_out ││ 3                                                 │
      │               ││──────────────────────────────────────────         │
      │               ││──────┬─────┬─────┬─────┬─────┬─────┬─────         │
      │out            ││ 00128│00129│00130│00131│00132│00133│00134         │
      │               ││──────┴─────┴─────┴─────┴─────┴─────┴─────         │
      └───────────────┘└───────────────────────────────────────────────────┘
      |}];
    let waves = test ~start_bcd:0x9 ~num_cycles:5 in
    Waveform.print ~wave_width:2 waves;
    [%expect
      {|
      ┌Signals────────┐┌Waves──────────────────────────────────────────────┐
      │clock          ││┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──│
      │               ││   └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  │
      │restart        ││──────┐                                            │
      │               ││      └───────────────────────────────────         │
      │               ││──────────────────────────────────────────         │
      │start_at       ││ 00009                                             │
      │               ││──────────────────────────────────────────         │
      │               ││──────┬───────────────────────────────────         │
      │num_digits_out ││ 1    │2                                           │
      │               ││──────┴───────────────────────────────────         │
      │               ││──────┬─────┬─────┬─────┬─────┬─────┬─────         │
      │out            ││ 00009│00010│00011│00012│00013│00014│00015         │
      │               ││──────┴─────┴─────┴─────┴─────┴─────┴─────         │
      └───────────────┘└───────────────────────────────────────────────────┘
      |}]
  ;;
end

module Replicator = struct
  let input_size_in_digits = Multidigit_bcd_counter.num_digits
  let input_size_in_bits = Multidigit_bcd_counter.num_bits
  let output_size_in_digits = Multidigit_bcd_counter.num_digits * 2
  let output_size_in_bits = Multidigit_bcd_counter.num_bits * 2

  module I = struct
    type 'a t =
      { input : 'a [@bits input_size_in_bits]
      ; num_digits : 'a [@bits 3]
      }
    [@@deriving hardcaml]
  end

  module O = struct
    type 'a t = { output : 'a [@bits output_size_in_bits] } [@@deriving hardcaml]
  end

  let create
    (type a)
    (module Comb : Comb.S with type t = a)
    ~replication_count
    { I.input; num_digits }
    =
    let open Comb in
    assert (Int.between replication_count ~low:1 ~high:10);
    (* I'm lazy to do multiplication by a constant the proper way *)
    let total_produced_digits = num_digits *: of_int_trunc ~width:4 replication_count in
    let overflow =
      total_produced_digits
      >: of_int_trunc ~width:(width total_produced_digits) output_size_in_digits
    in
    let input = uresize input ~width:output_size_in_bits in
    let output =
      mux2
        overflow
        (zero output_size_in_bits)
        (List.init replication_count ~f:(fun i ->
           log_shift ~f:(fun input ~by -> sll input ~by:(by * 4 * i)) input ~by:num_digits)
         |> List.reduce_balanced_exn ~f:( |: ))
    in
    { O.output }
  ;;

  let%expect_test _ =
    let test ~input ~replication_count =
      let num_digits =
        if input = 0 then 0 else String.length (Int.Hex.to_string input) - 2
      in
      let { O.output } =
        create
          (module Bits)
          ~replication_count
          { input = Bits.of_int_trunc ~width:input_size_in_bits input
          ; num_digits = Bits.of_int_trunc ~width:3 num_digits
          }
      in
      print_s [%sexp (output : Bits.Hex.t)]
    in
    test ~input:0x1 ~replication_count:3;
    [%expect {| 40'h0000000111 |}];
    test ~input:0x15 ~replication_count:3;
    [%expect {| 40'h0000151515 |}];
    test ~input:0x99999 ~replication_count:2;
    [%expect {| 40'h9999999999 |}];
    test ~input:0x99999 ~replication_count:3;
    [%expect {| 40'h0000000000 |}]
  ;;

  let create = create (module Signal)
end

module Counter = struct
  let digit_count = Replicator.output_size_in_digits
  let bit_count = Replicator.output_size_in_bits
  let num_concurrent = 40
  (* Should be able to fit in all our inputs. Otherwise I can do a fifo, and add a reset. *)

  let count_size = 64

  module Range = struct
    type 'a t =
      { lo : 'a [@bits bit_count]
      ; hi : 'a [@bits bit_count]
      }
    [@@deriving hardcaml]
  end

  module I = struct
    type 'a t =
      { clock : 'a
      ; ranges : 'a Range.t iarray [@length num_concurrent]
      ; ranges_ready : 'a
      }
    [@@deriving hardcaml]
  end

  module O = struct
    type 'a t =
      { count : 'a
           [@bits count_size] (* Should fit in count_size bits. In practice a lot less *)
      ; ready : 'a
      }
    [@@deriving hardcaml]
  end

  let freeze_when_ready { O.count; ready } ~clock =
    let ready_out = wire 1 in
    let ready = ready |: ready_out in
    let ready_reg = reg ~initialize_to:(Bits.zero 1) (Reg_spec.create ~clock ()) ready in
    assign ready_out ready_reg;
    let count_out = wire count_size in
    let count = mux2 ready (mux2 ready_out count_out count) (zero count_size) in
    let count_reg = reg (Reg_spec.create ~clock ()) count in
    assign count_out count_reg;
    { O.count; ready }
  ;;

  let sample_input =
    "11-22,95-115,998-1012,1188511880-1188511890,222220-222224,1698522-1698528,446443-446449,38593856-38593862,565653-565659,824824821-824824827,2121212118-2121212124\n"
  ;;

  module Input_parser = struct
    module I = struct
      type 'a t =
        { char : 'a [@bits 8]
        ; clock : 'a
        }
      [@@deriving hardcaml]
    end

    module O = struct
      type 'a t =
        { ranges : 'a Range.t iarray [@length num_concurrent]
        ; ranges_ready : 'a
        }
      [@@deriving hardcaml]
    end

    let create { I.char; clock } =
      let ranges =
        Iarray.init num_concurrent ~f:(fun _ ->
          let init_digits () =
            Always.Variable.reg
              ~width:bit_count
              ~initialize_to:(Bits.zero bit_count)
              (Reg_spec.create ~clock ())
          in
          { Range.lo = init_digits (); hi = init_digits () })
      in
      let accumulator =
        Always.Variable.reg
          ~width:bit_count
          (Reg_spec.create ~clock ())
          ~initialize_to:(Bits.zero bit_count)
      in
      let ready =
        Always.Variable.reg ~initialize_to:Bits.gnd ~width:1 (Reg_spec.create ~clock ())
      in
      let current_range =
        Always.Variable.reg
          ~width:(num_bits_to_represent num_concurrent)
          (Reg_spec.create ~clock ())
          ~initialize_to:(Bits.zero (num_bits_to_represent num_concurrent))
      in
      let reset_accumulator = Always.(accumulator <--. 0) in
      let update_range f =
        Always.switch
          current_range.value
          (List.init num_concurrent ~f:(fun i ->
             let index = of_int_trunc i ~width:(num_bits_to_represent num_concurrent) in
             index, f (Iarray.get ranges i)))
      in
      let set_lo =
        update_range (fun range -> Always.[ range.lo <-- accumulator.value ])
      in
      let set_hi =
        update_range (fun range -> Always.[ range.hi <-- accumulator.value ])
      in
      Always.compile
        [ Always.switch
            char
            (List.filter_map Char.all ~f:(fun c ->
               let%map.Option actions =
                 match c with
                 | '0' .. '9' ->
                   let digit = Char.get_digit_exn c in
                   Some
                     Always.
                       [ accumulator
                         <-- (sll accumulator.value ~by:4
                              |: of_int_trunc ~width:bit_count digit)
                       ]
                 | '-' -> Some [ set_lo; reset_accumulator ]
                 | ',' -> Some [ set_hi; reset_accumulator; Always.incr current_range ]
                 | '\n' -> Some [ Always.(ready <-- vdd); set_hi ]
                 | _ -> None
               in
               of_char c, actions))
        ];
      let ranges =
        Iarray.map ranges ~f:(fun { Range.lo; hi } ->
          { Range.lo = lo.value; hi = hi.value })
      in
      { O.ranges; ranges_ready = ready.value }
    ;;

    let%expect_test _ =
      let module Test_circuit = Circuit.With_interface (I) (O) in
      let simulator = Cyclesim.create (Test_circuit.create_exn ~name:"input" create) in
      let waves, simulator = Waveform.create simulator in
      let char = Cyclesim.in_port simulator "char" in
      String.iter sample_input ~f:(fun c ->
        char := Bits.of_char c;
        Cyclesim.cycle simulator);
      Cyclesim.cycle simulator;
      Cyclesim.cycle simulator;
      Waveform.print ~start_cycle:(String.length sample_input - 2) waves;
      [%expect
        {|
        ┌Signals────────┐┌Waves──────────────────────────────────────────────┐
        │clock          ││┌───┐   ┌───┐   ┌───┐   ┌───┐   ┌───┐   ┌───┐   ┌──│
        │               ││    └───┘   └───┘   └───┘   └───┘   └───┘   └───┘  │
        │               ││────────┬───────────────────────                   │
        │char           ││ 34     │0A                                        │
        │               ││────────┴───────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi0     ││ 0000000022                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi1     ││ 0000000115                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────┬───────────────                   │
        │ranges$hi10    ││ 0000000000     │2121212124                        │
        │               ││────────────────┴───────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi11    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi12    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi13    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi14    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi15    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi16    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi17    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi18    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi19    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi2     ││ 0000001012                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi20    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi21    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi22    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi23    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi24    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi25    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi26    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi27    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi28    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi29    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi3     ││ 1188511890                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi30    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi31    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi32    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi33    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi34    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi35    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi36    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi37    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi38    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi39    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi4     ││ 0000222224                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi5     ││ 0001698528                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi6     ││ 0000446449                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi7     ││ 0038593862                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi8     ││ 0000565659                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$hi9     ││ 0824824827                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo0     ││ 0000000011                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo1     ││ 0000000095                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo10    ││ 2121212118                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo11    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo12    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo13    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo14    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo15    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo16    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo17    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo18    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo19    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo2     ││ 0000000998                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo20    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo21    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo22    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo23    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo24    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo25    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo26    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo27    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo28    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo29    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo3     ││ 1188511880                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo30    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo31    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo32    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo33    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo34    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo35    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo36    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo37    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo38    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo39    ││ 0000000000                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo4     ││ 0000222220                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo5     ││ 0001698522                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo6     ││ 0000446443                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo7     ││ 0038593856                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo8     ││ 0000565653                                        │
        │               ││────────────────────────────────                   │
        │               ││────────────────────────────────                   │
        │ranges$lo9     ││ 0824824821                                        │
        │               ││────────────────────────────────                   │
        │ranges_ready   ││                ┌───────────────                   │
        │               ││────────────────┘                                  │
        └───────────────┘└───────────────────────────────────────────────────┘
        |}]
    ;;
  end

  let bcd_to_binary input =
    List.init digit_count ~f:(fun i ->
      input.:[(i * 4) + 3, i * 4] *: of_int_trunc ~width:(count_size - 4) (Int.pow 10 i))
    |> List.reduce_exn ~f:( +: )
  ;;

  let%expect_test _ =
    let open Bits in
    let bcd_to_binary input =
      let input = of_int_trunc ~width:40 input in
      List.init digit_count ~f:(fun i ->
        input.:[(i * 4) + 3, i * 4] *: of_int_trunc ~width:(count_size - 4) (Int.pow 10 i))
      |> List.reduce_exn ~f:( +: )
      |> to_int_trunc
      |> Int.to_string
      |> print_endline
    in
    bcd_to_binary 0x1234;
    [%expect {| 1234 |}];
    bcd_to_binary 0x1234560;
    [%expect {| 1234560 |}]
  ;;

  module Part1 = struct
    let create { I.clock; ranges; ranges_ready } =
      let max_hi =
        Iarray.map ranges ~f:(fun { Range.hi; _ } -> hi)
        |> Iarray.reduce_exn ~f:(fun a b -> mux2 (a >: b) a b)
      in
      let restart =
        reg ~initialize_to:Bits.vdd ~clear:ranges_ready (Reg_spec.create ~clock ()) vdd
      in
      let counter =
        Multidigit_bcd_counter.create
          { Multidigit_bcd_counter.I.start_at = of_int_trunc ~width:bit_count 0
          ; restart
          ; clock
          }
      in
      let replicated =
        Replicator.create
          ~replication_count:2
          { input = counter.out; num_digits = counter.num_digits_out }
      in
      let ready = ranges_ready &: (replicated.output >: max_hi) in
      let invalid =
        Iarray.map ranges ~f:(fun { Range.lo; hi } ->
          replicated.output >=: lo &: (replicated.output <=: hi))
        |> Iarray.reduce_exn ~f:( |: )
      in
      let count = wire count_size in
      let count_reg =
        reg (Reg_spec.create ~clock ()) count ~initialize_to:(Bits.zero count_size)
      in
      let count_in =
        mux2
          (restart |: ~:invalid)
          count_reg
          (count_reg +: bcd_to_binary replicated.output)
      in
      assign count count_in;
      freeze_when_ready { O.count; ready } ~clock
    ;;

    let create input =
      let%tydi { ranges; ranges_ready } = Input_parser.create input in
      create { I.clock = input.clock; ranges; ranges_ready }
    ;;

    let%expect_test _ =
      let module Test_circuit = Circuit.With_interface (Input_parser.I) (O) in
      let simulator = Cyclesim.create (Test_circuit.create_exn ~name:"input" create) in
      let char = Cyclesim.in_port simulator "char" in
      let ready = Cyclesim.out_port simulator "ready" in
      let count = Cyclesim.out_port simulator "count" in
      String.iter sample_input ~f:(fun c ->
        char := Bits.of_char c;
        Cyclesim.cycle simulator);
      Cyclesim.cycle ~n:100_005 simulator;
      print_s [%message (ready : Bits.t ref) (count : Bits.Unsigned_int.t ref)];
      [%expect {| ((ready 1) (count 64'd1227775554)) |}]
    ;;

    let%expect_test _ =
      let module Test_circuit = Circuit.With_interface (Input_parser.I) (O) in
      let simulator = Cyclesim.create (Test_circuit.create_exn ~name:"input" create) in
      let char = Cyclesim.in_port simulator "char" in
      let ready = Cyclesim.out_port simulator "ready" in
      let count = Cyclesim.out_port simulator "count" in
      String.iter (In_channel.read_all "../inputs/day2") ~f:(fun c ->
        char := Bits.of_char c;
        Cyclesim.cycle simulator);
      Cyclesim.cycle ~n:100_005 simulator;
      print_s [%message (ready : Bits.t ref) (count : Bits.Unsigned_int.t ref)];
      [%expect {| ((ready 1) (count 64'd24043483400)) |}]
    ;;
  end

  let number_expressible_using_smaller_repeats ~number ~num_digits =
    let ( .::() ) number i = number.:[(i * 4) + 3, i * 4] in
    mux_init num_digits 6 ~f:(function
      | 2 -> number.::(0) ==: number.::(1)
      | 3 -> number.::(0) ==: number.::(1) &: (number.::(1) ==: number.::(2))
      | 4 ->
        number.::(0) ==: number.::(2) &: (number.::(1) ==: number.::(3))
        (* 2 can make it up *)
      | 5 ->
        number.::(0)
        ==: number.::(1)
        &: (number.::(1) ==: number.::(2))
        &: (number.::(2) ==: number.::(3))
        &: (number.::(3) ==: number.::(4))
      | _ -> gnd)
  ;;

  module Part2 = struct
    let create { I.clock; ranges; ranges_ready } =
      let max_hi =
        Iarray.map ranges ~f:(fun { Range.hi; _ } -> hi)
        |> Iarray.reduce_exn ~f:(fun a b -> mux2 (a >: b) a b)
      in
      let restart =
        reg ~initialize_to:Bits.vdd ~clear:ranges_ready (Reg_spec.create ~clock ()) vdd
      in
      let counter =
        Multidigit_bcd_counter.create
          { Multidigit_bcd_counter.I.start_at = of_int_trunc ~width:bit_count 0
          ; restart
          ; clock
          }
      in
      let replicated =
        List.init 9 ~f:(fun i ->
          let replication_count = i + 2 in
          Replicator.create
            ~replication_count
            { input = counter.out; num_digits = counter.num_digits_out })
      in
      let ready = ranges_ready &: ((List.hd_exn replicated).output >: max_hi) in
      let sum_invalid =
        List.map replicated ~f:(fun replicated ->
          let invalid =
            Iarray.map ranges ~f:(fun { Range.lo; hi } ->
              replicated.output >=: lo &: (replicated.output <=: hi))
            |> Iarray.reduce_exn ~f:( |: )
          in
          mux2 invalid (bcd_to_binary replicated.output) (zero count_size))
        |> List.reduce_balanced_exn ~f:( +: )
      in
      let count = wire count_size in
      let count_reg =
        reg (Reg_spec.create ~clock ()) count ~initialize_to:(Bits.zero count_size)
      in
      let count_in =
        mux2
          (restart
           |: number_expressible_using_smaller_repeats
                ~number:counter.out
                ~num_digits:counter.num_digits_out)
          count_reg
          (count_reg +: sum_invalid)
      in
      assign count count_in;
      freeze_when_ready { O.count; ready } ~clock
    ;;

    let create input =
      let%tydi { ranges; ranges_ready } = Input_parser.create input in
      create { I.clock = input.clock; ranges; ranges_ready }
    ;;

    let%expect_test _ =
      let module Test_circuit = Circuit.With_interface (Input_parser.I) (O) in
      let simulator = Cyclesim.create (Test_circuit.create_exn ~name:"input" create) in
      let char = Cyclesim.in_port simulator "char" in
      let ready = Cyclesim.out_port simulator "ready" in
      let count = Cyclesim.out_port simulator "count" in
      String.iter sample_input ~f:(fun c ->
        char := Bits.of_char c;
        Cyclesim.cycle simulator);
      Cyclesim.cycle ~n:100_005 simulator;
      print_s [%message (ready : Bits.t ref) (count : Bits.Unsigned_int.t ref)];
      [%expect {| ((ready 1) (count 64'd4174379265)) |}]
    ;;

    let%expect_test _ =
      let module Test_circuit = Circuit.With_interface (Input_parser.I) (O) in
      let simulator = Cyclesim.create (Test_circuit.create_exn ~name:"input" create) in
      let char = Cyclesim.in_port simulator "char" in
      let ready = Cyclesim.out_port simulator "ready" in
      let count = Cyclesim.out_port simulator "count" in
      String.iter (In_channel.read_all "../inputs/day2") ~f:(fun c ->
        char := Bits.of_char c;
        Cyclesim.cycle simulator);
      Cyclesim.cycle ~n:100_005 simulator;
      print_s [%message (ready : Bits.t ref) (count : Bits.Unsigned_int.t ref)];
      [%expect {| ((ready 1) (count 64'd38262920235)) |}]
    ;;
  end
end
