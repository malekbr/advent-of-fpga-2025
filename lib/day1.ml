open! Core
open! Hardcaml
open Hardcaml.Signal
open Hardcaml_waveterm

(* All our input numbers are 3 digits long, and our input is O(1000) lines
   long, so our computation and results should comfortably fit in 16 bits. *)

(* Idea: 
   1. create a custom 7 bit adder, base 100. If output >= 100, remove 100,
   set carry out bit to 1.
   2. Any input number is split into segments, n / 100, and n % 100.
   We use magic number computation for division by 100. I used godbolt
   to find the number, but see here for reasoning: https://stackoverflow.com/questions/24628899/understanding-of-msvs-c-compiler-optimizations.
   In 16 bits, the compiler formula is, computed in 32 bits and taking the higher 16 bits
   is (n shr 2) * 5243 shr 1. (multiplication is signed)
   3. We compute remainder by doing an unsigned multiply by 100, then subtracting. Only need
   to take the lower 7 bits.
   4. We pick an arbitrary direction as positive, say L. If L, we keep the remainder as is.
   If R, we take 100 - remainder. The direction does not affect the higher bits resulting
   from the division.
   4. For part 1, we only keep the remainder, and ignore the carry. If the remainder is 0
   at the end of an input line, we increment the count.
   5. For part 2, we add the result of the division to our total, + the result of the carry
   bit.
*)

module Div_100 = struct
  module I = struct
    type 'a t = { input : 'a [@bits 16] } [@@deriving hardcaml]
  end

  module O = struct
    type 'a t =
      { quotient : 'a [@bits 10]
      ; remainder : 'a [@bits 7]
      }
    [@@deriving hardcaml]
  end

  let compute { I.input } =
    let multiplied = srl input ~by:2 *: of_int_trunc ~width:16 5243 in
    let quotient = multiplied.:[26, 17] in
    let remainder = (input -: (quotient *: of_int_trunc ~width:7 100).:[15, 0]).:[6, 0] in
    { O.quotient; remainder }
  ;;

  let test () =
    let module Test_circuit = Circuit.With_interface (I) (O) in
    let simulator = Cyclesim.create (Test_circuit.create_exn ~name:"div_100" compute) in
    let waves, sim = Waveform.create simulator in
    let input = Cyclesim.in_port sim "input" in
    List.iter [ 0; 1; 10; 15; 100; 120; 156; 65535 ] ~f:(fun x ->
      input := Bits.of_int_trunc ~width:16 x;
      Cyclesim.cycle sim);
    waves
  ;;

  let%expect_test _ =
    let waves = test () in
    Waveform.print
      ~display_width:90
      ~display_rules:Display_rule.[ custom ~f:(fun _ -> Some Unsigned_int) ]
      waves;
    [%expect
      {|
      ┌Signals───────────┐┌Waves───────────────────────────────────────────────────────────────┐
      │                  ││────────┬───────┬───────┬───────┬───────┬───────┬───────┬───────    │
      │input             ││ 0      │1      │10     │15     │100    │120    │156    │65535      │
      │                  ││────────┴───────┴───────┴───────┴───────┴───────┴───────┴───────    │
      │                  ││────────────────────────────────┬───────────────────────┬───────    │
      │quotient          ││ 0                              │1                      │655        │
      │                  ││────────────────────────────────┴───────────────────────┴───────    │
      │                  ││────────┬───────┬───────┬───────┬───────┬───────┬───────┬───────    │
      │remainder         ││ 0      │1      │10     │15     │0      │20     │56     │35         │
      │                  ││────────┴───────┴───────┴───────┴───────┴───────┴───────┴───────    │
      └──────────────────┘└────────────────────────────────────────────────────────────────────┘
      |}]
  ;;
end

module Base_100_adder = struct
  module I = struct
    type 'a t =
      { a : 'a [@bits 7]
      ; b : 'a [@bits 7]
      }
    [@@deriving hardcaml]
  end

  module O = struct
    type 'a t =
      { sum : 'a [@bits 7]
      ; carry : 'a [@bits 1]
      }
    [@@deriving hardcaml]
  end

  let compute { I.a; b } =
    let sum = uresize a ~width:8 +: uresize b ~width:8 in
    let b8_100 = of_int_trunc ~width:8 100 in
    let carry = sum >=: b8_100 in
    let sum = (mux2 carry (sum -: b8_100) sum).:[6, 0] in
    { O.sum; carry }
  ;;

  let test () =
    let module Test_circuit = Circuit.With_interface (I) (O) in
    let simulator =
      Cyclesim.create (Test_circuit.create_exn ~name:"base_100_adder" compute)
    in
    let waves, sim = Waveform.create simulator in
    let a = Cyclesim.in_port sim "a" in
    let b = Cyclesim.in_port sim "b" in
    let inputs = List.map [ 0; 1; 50; 99 ] ~f:(Bits.of_int_trunc ~width:7) in
    List.cartesian_product inputs inputs
    |> List.iter ~f:(fun (a_val, b_val) ->
      a := a_val;
      b := b_val;
      Cyclesim.cycle sim);
    waves
  ;;

  let%expect_test _ =
    let waves = test () in
    Waveform.print
      ~display_width:90
      ~wave_width:1
      ~display_rules:Display_rule.[ custom ~f:(fun _ -> Some Unsigned_int) ]
      waves;
    [%expect
      {|
      ┌Signals───────────┐┌Waves───────────────────────────────────────────────────────────────┐
      │                  ││────────────────┬───────────────┬───────────────┬───────────────    │
      │a                 ││ 0              │1              │50             │99                 │
      │                  ││────────────────┴───────────────┴───────────────┴───────────────    │
      │                  ││────┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───    │
      │b                 ││ 0  │1  │50 │99 │0  │1  │50 │99 │0  │1  │50 │99 │0  │1  │50 │99     │
      │                  ││────┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───    │
      │                  ││────────────────────────────┬───┬───────┬───────┬───┬───────────    │
      │carry             ││ 0                          │1  │0      │1      │0  │1              │
      │                  ││────────────────────────────┴───┴───────┴───────┴───┴───────────    │
      │                  ││────┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───    │
      │sum               ││ 0  │1  │50 │99 │1  │2  │51 │0  │50 │51 │0  │49 │99 │0  │49 │98     │
      │                  ││────┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───    │
      └──────────────────┘└────────────────────────────────────────────────────────────────────┘
      |}]
  ;;
end

let test_input = {|L68
L30
R48
L5
R60
L55
L1
L99
R14
L82
|}

let input_testbench input_text sim =
  let input = Cyclesim.in_port sim "char_in" in
  String.iter input_text ~f:(fun c ->
    input := Bits.of_char c;
    Cyclesim.cycle sim);
  input := Bits.of_char '\000';
  Cyclesim.cycle sim;
  Cyclesim.cycle sim
;;

module Input_parser = struct
  module Direction = struct
    type t =
      | L
      | R
    [@@deriving sexp_of, compare ~localize, enumerate]

    include functor Hardcaml.Enum.Make_enums
  end

  module I = struct
    type 'a t =
      { char_in : 'a [@bits 8]
      ; clock : 'a
      }
    [@@deriving hardcaml]
  end

  module O = struct
    type 'a t =
      { num_out : 'a [@bits 16]
      ; sign : 'a Direction.Binary.t
      ; ready : 'a
      }
    [@@deriving hardcaml]
  end

  let create { I.char_in; I.clock } =
    let reg_spec = Reg_spec.create ~clock () in
    let sign = Direction.Binary.Of_always.reg (Reg_spec.create ~clock ()) in
    let num_out = Always.Variable.reg ~width:16 reg_spec in
    let ready = Always.Variable.reg ~width:1 reg_spec in
    Always.(
      compile
        [ ready <-- (char_in ==: of_char '\n')
        ; switch
            char_in
            (List.map Direction.all ~f:(fun dir ->
               let char =
                 match dir with
                 | L -> 'L'
                 | R -> 'R'
               in
               ( of_char char
               , [ Direction.Binary.Of_always.assign
                     sign
                     (Direction.Binary.of_enum (module Signal) dir)
                 ; num_out <--. 0
                 ] ))
             @ List.init 10 ~f:(fun i ->
               ( of_char (Char.of_int_exn (i + Char.to_int '0'))
               , [ num_out
                   <-- (Variable.value num_out *: of_int_trunc 10 ~width:16).:[15, 0]
                       +: of_int_trunc i ~width:16
                 ] )))
        ]);
    { O.num_out = Always.Variable.value num_out
    ; sign = Direction.Binary.Of_always.value sign
    ; ready = Always.Variable.value ready
    }
  ;;

  let test () =
    let module Test_circuit = Circuit.With_interface (I) (O) in
    let simulator =
      Cyclesim.create (Test_circuit.create_exn ~name:"input_parser" create)
    in
    let waves, sim = Waveform.create simulator in
    input_testbench test_input sim;
    waves
  ;;

  let%expect_test _ =
    let waves = test () in
    Waveform.print
      ~display_width:200
      ~wave_width:1
      ~display_rules:
        Display_rule.
          [ port_name_is
              "char_in"
              ~wave_format:(Custom (fun bits -> Bits.to_char bits |> Char.escaped))
          ; port_name_is "num_out" ~wave_format:Unsigned_int
          ; Default
          ]
      waves;
    [%expect
      {|
      ┌Signals───────────┐┌Waves─────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┐
      │                  ││────┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───────┬───┬───┬───┬───┬───┬───────┬───┬───┬───┬───┬───┬───┬───┬───┬───┬───────                  │
      │char_in           ││ L  │6  │8  │\n │L  │3  │0  │\n │R  │4  │8  │\n │L  │5  │\n │R  │6  │0  │\n │L  │5      │\n │L  │1  │\n │L  │9      │\n │R  │1  │4  │\n │L  │8  │2  │\n │\000                     │
      │                  ││────┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───────┴───┴───┴───┴───┴───┴───────┴───┴───┴───┴───┴───┴───┴───┴───┴───┴───────                  │
      │                  ││────────┬───┬───────┬───┬───┬───────┬───┬───┬───────┬───┬───────┬───┬───┬───────┬───┬───┬───────┬───┬───────┬───┬───┬───────┬───┬───┬───────┬───┬───┬───────────                  │
      │num_out           ││ 0      │6  │68     │0  │3  │30     │0  │4  │48     │0  │5      │0  │6  │60     │0  │5  │55     │0  │1      │0  │9  │99     │0  │1  │14     │0  │8  │82                           │
      │                  ││────────┴───┴───────┴───┴───┴───────┴───┴───┴───────┴───┴───────┴───┴───┴───────┴───┴───┴───────┴───┴───────┴───┴───┴───────┴───┴───┴───────┴───┴───┴───────────                  │
      │clock             ││┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─│
      │                  ││  └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ └─┘ │
      │ready             ││                ┌───┐           ┌───┐           ┌───┐       ┌───┐           ┌───┐           ┌───┐       ┌───┐           ┌───┐           ┌───┐           ┌───┐                     │
      │                  ││────────────────┘   └───────────┘   └───────────┘   └───────┘   └───────────┘   └───────────┘   └───────┘   └───────────┘   └───────────┘   └───────────┘   └───                  │
      │                  ││────────────────────────────────────┬───────────────┬───────────┬───────────────┬───────────────────────────────────────────┬───────────────┬───────────────────                  │
      │sign$binary_varian││ L                                  │R              │L          │R              │L                                          │R              │L                                    │
      │                  ││────────────────────────────────────┴───────────────┴───────────┴───────────────┴───────────────────────────────────────────┴───────────────┴───────────────────                  │
      └──────────────────┘└──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────┘
      |}]
  ;;
end

module Part_1 = struct
  module I = Input_parser.I

  module O = struct
    type 'a t = { password : 'a [@bits 16] } [@@deriving hardcaml]
  end

  let create input =
    let%tydi { num_out; sign; ready } = Input_parser.create input in
    let password =
      Always.Variable.reg ~enable:ready ~width:16 (Reg_spec.create ~clock:input.clock ())
    in
    let accumulator =
      Always.Variable.reg
        ~initialize_to:(Bits.of_int_trunc 50 ~width:7)
        ~enable:ready
        ~width:7
        (Reg_spec.create ~clock:input.clock ())
    in
    let%tydi { quotient = _; remainder } = Div_100.compute { input = num_out } in
    let to_add =
      Input_parser.Direction.Binary.match_
        (module Signal)
        sign
        [ L, remainder
        ; R, mux2 (remainder ==: zero 7) remainder (of_int_trunc 100 ~width:7 -: remainder)
        ]
    in
    let%tydi { sum = updated_accumulator; carry = _ } =
      Base_100_adder.compute { a = Always.Variable.value accumulator; b = to_add }
    in
    let current_password = Always.Variable.value password in
    let updated_password =
      mux2 (updated_accumulator ==: zero 7) (incr current_password) current_password
    in
    Always.(
      compile [ password <-- updated_password; accumulator <-- updated_accumulator ]);
    { O.password = current_password }
  ;;

  let test input =
    let module Test_circuit = Circuit.With_interface (I) (O) in
    let sim = Cyclesim.create (Test_circuit.create_exn ~name:"input_parser" create) in
    input_testbench input sim;
    Bits.to_unsigned_int !(Cyclesim.out_port sim "password") |> [%sexp_of: int] |> print_s
  ;;

  let%expect_test "Sample" =
    test test_input;
    [%expect {| 3 |}];
    In_channel.read_all "../inputs/day1" |> test;
    [%expect {| 1059 |}]
  ;;
end

module Part_2 = struct
  module I = Input_parser.I

  module O = struct
    type 'a t = { password : 'a [@bits 16] } [@@deriving hardcaml]
  end

  let create input =
    let%tydi { num_out; sign; ready } = Input_parser.create input in
    let password =
      Always.Variable.reg ~enable:ready ~width:16 (Reg_spec.create ~clock:input.clock ())
    in
    let accumulator =
      Always.Variable.reg
        ~initialize_to:(Bits.of_int_trunc 50 ~width:7)
        ~enable:ready
        ~width:7
        (Reg_spec.create ~clock:input.clock ())
    in
    let%tydi { quotient; remainder } = Div_100.compute { input = num_out } in
    let to_add =
      Input_parser.Direction.Binary.match_
        (module Signal)
        sign
        [ L, remainder
        ; R, mux2 (remainder ==: zero 7) remainder (of_int_trunc 100 ~width:7 -: remainder)
        ]
    in
    let%tydi { sum = updated_accumulator; carry } =
      Base_100_adder.compute { a = Always.Variable.value accumulator; b = to_add }
    in
    let current_password = Always.Variable.value password in
    let updated_password =
      current_password +: uresize quotient ~width:16 +: uresize carry ~width:16
    in
    Always.(
      compile [ password <-- updated_password; accumulator <-- updated_accumulator ]);
    { O.password = current_password }
  ;;

  let test input =
    let module Test_circuit = Circuit.With_interface (I) (O) in
    let sim = Cyclesim.create (Test_circuit.create_exn ~name:"input_parser" create) in
    input_testbench input sim;
    Bits.to_unsigned_int !(Cyclesim.out_port sim "password") |> [%sexp_of: int] |> print_s
  ;;

  let%expect_test "Sample" =
    test test_input;
    [%expect {| 5 |}];
    In_channel.read_all "../inputs/day1" |> test;
    [%expect {| 6305 |}]
  ;;
end
