(*
   Test/Example for Maximum Subarray
*)

module Test.MaxSubarray

open CLRS.Ch04.MaxSubarray.Kadane
open FStar.IO
open FStar.All

// Example: array [-2, 1, -3, 4, -1, 2, 1, -5, 4]
// Maximum subarray is [4, -1, 2, 1] with sum 6

let test_example () : ML unit =
  print_string "Maximum Subarray Test\n";
  print_string "=====================\n";
  print_string "This module demonstrates Kadane's algorithm\n";
  print_string "Finding the contiguous subarray with maximum sum\n";
  print_string "\nExample: [-2, 1, -3, 4, -1, 2, 1, -5, 4]\n";
  print_string "Maximum subarray: [4, -1, 2, 1] = 6\n"

#push-options "--warn_error -272"
let main = test_example ()
#pop-options
