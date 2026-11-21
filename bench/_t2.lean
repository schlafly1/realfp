example (x : Int) (h : x < 0) : compare x 0 = .lt := by exact?
example (x : Int) (h : 0 < x) : compare x 0 = .gt := by exact?
example (x : Int) (h : x = 0) : compare x 0 = .eq := by exact?
