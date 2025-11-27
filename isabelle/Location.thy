theory Location
  imports Main
begin

(* file, begin line, col, end line, col *)
datatype Location = Location string int int int int


(* Dummy location *)
definition no_loc :: Location where
  "no_loc = Location '''' 0 0 0 0"


(* True if a location is "empty" (zero-width) *)
fun is_location_empty :: "Location \<Rightarrow> bool" where
  "is_location_empty (Location _ line1 col1 line2 col2) = (line1 = line2 \<and> col1 = col2)"


(* Get a zero-sized location corresponding to the *end* of the given location *)
fun get_location_end :: "Location \<Rightarrow> Location" where
  "get_location_end (Location filename _ _ line col) = Location filename line col line col"


(* Merge locations using the following logic:
    - If location 1 is empty, use location 2
    - Otherwise, take filename & start pos from location 1, and end pos from location 2
   This logic seems to give reasonably good error positions when used with the BasicParser.
*)
fun merge_locations :: "Location \<Rightarrow> Location \<Rightarrow> Location"
  where
"merge_locations loc1 loc2 = 
  (if is_location_empty loc1 then loc2
   else (case (loc1, loc2) of
          (Location filename line1 col1 _ _, Location _ _ _ line2 col2) \<Rightarrow>
            Location filename line1 col1 line2 col2))"


(* Determine if (line1,col1) is after (line2,col2) *)
fun line_col_after :: "int \<times> int \<Rightarrow> int \<times> int \<Rightarrow> bool" where
  "line_col_after (line1, col1) (line2, col2) = 
    ((line1 > line2) \<or> (line1 = line2 \<and> col1 > col2))"


(* Find the "max" of two locations (assumed to be in same file),
   where "max" means the one starting most to the right, or (if they both start at the same
   place) then the one ending most to the right. *)
definition max_location :: "Location \<Rightarrow> Location \<Rightarrow> Location"
  where
"max_location loc1 loc2 = 
  (case (loc1, loc2) of
    (Location _ begin_line_1 begin_col_1 end_line_1 end_col_1, 
     Location _ begin_line_2 begin_col_2 end_line_2 end_col_2) \<Rightarrow>
      if line_col_after (begin_line_2, begin_col_2) (begin_line_1, begin_col_1) then 
        loc2
      else if (begin_line_1 = begin_line_2 \<and> begin_col_1 = begin_col_2 \<and>
               line_col_after (end_line_2, end_col_2) (end_line_1, end_col_1)) then
        loc2
      else
        loc1)"

end
