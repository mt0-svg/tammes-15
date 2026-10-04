import Tammes15.D3Ck2.Prog.F1L
import Tammes15.D3Prog.Sem

namespace D3Prog

open D3Ck2Spec D3Ck2 Lanes24

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option linter.unusedVariables false in
theorem progF1L_seg3 (F0 F1 F2 F3 H0 H1 H2 : ℕ) (hb_F0 : F0 < 2 ^ 64) (hb_F1 : F1 < 2 ^ 64) (hb_F2 : F2 < 2 ^ 64) (hb_F3 : F3 < 2 ^ 64) (hb_H0 : H0 < 2 ^ 64) (hb_H1 : H1 < 2 ^ 64) (hb_H2 : H2 < 2 ^ 64) (v13 : ℕ) (v110 : ℕ) (v270 : ℕ) (v423 : ℕ) (v471 : ℕ) (v485 : ℕ) (v593 : ℕ) (v783 : ℕ) (v1005 : ℕ) (v1012 : ℕ) (v1013 : ℕ) (v1045 : ℕ) (v1084 : ℕ) (v1139 : ℕ) (v1187 : ℕ) (v1193 : ℕ) (v1351 : ℕ) (v1397 : ℕ) (v1417 : ℕ) (v1531 : ℕ) (v1702 : ℕ) (v1897 : ℕ) (v1904 : ℕ) (h_v13 : R 1 0 0 1 v13 v13) (h_v110 : R 1 0 0 1 v110 v110) (h_v270 : R 1 0 0 1 v270 v270) (h_v423 : R 1 0 0 1 v423 v423) (h_v471 : R 1 0 0 1 v471 v471) (h_v485 : R 1 0 0 1 v485 v485) (h_v593 : R 1 0 0 1 v593 v593) (h_v783 : R 1 0 0 1 v783 v783) (h_v1005 : R 1 0 0 1 v1005 v1005) (h_v1012 : R 1 0 0 1 v1012 v1012) (h_v1013 : R 1 0 0 1 v1013 v1013) (h_v1045 : R 1 0 0 1 v1045 v1045) (h_v1084 : R 1 0 0 1 v1084 v1084) (h_v1139 : R 1 0 0 1 v1139 v1139) (h_v1187 : R 1 0 0 1 v1187 v1187) (h_v1193 : R 1 0 0 1 v1193 v1193) (h_v1351 : R 1 0 0 1 v1351 v1351) (h_v1397 : R 1 0 0 1 v1397 v1397) (h_v1417 : R 1 0 0 1 v1417 v1417) (h_v1531 : R 1 0 0 1 v1531 v1531) (h_v1702 : R 1 0 0 1 v1702 v1702) (h_v1897 : R 1 0 0 1 v1897 v1897) (h_v1904 : R 1 0 0 1 v1904 v1904) :
    let v1905 := Nat.land v110 v1904
    let v1906 := Nat.land v270 v1905
    let v1907 := Nat.land v270 v1906
    let v1908 := Nat.land v13 v1907
    let v1909 := Nat.land v423 v1908
    let v1910 := Nat.land v471 v1909
    let v1911 := Nat.land v485 v1910
    let v1912 := Nat.land v593 v1911
    let v1913 := Nat.land v783 v1912
    let v1914 := Nat.land v1005 v1913
    let v1915 := Nat.land v1012 v1914
    let v1916 := Nat.land v1013 v1915
    let v1917 := Nat.land v1045 v1916
    let v1918 := Nat.land v1045 v1917
    let v1919 := Nat.land v1084 v1918
    let v1920 := Nat.land v13 v1919
    let v1921 := Nat.land v1139 v1920
    let v1922 := Nat.land v1187 v1921
    let v1923 := Nat.land v13 v1922
    let v1924 := Nat.land v110 v1923
    let v1925 := Nat.land v110 v1924
    let v1926 := Nat.land v1193 v1925
    let v1927 := Nat.land v1193 v1926
    let v1928 := Nat.land v13 v1927
    let v1929 := Nat.land v1351 v1928
    let v1930 := Nat.land v1397 v1929
    let v1931 := Nat.land v1417 v1930
    let v1932 := Nat.land v1531 v1931
    let v1933 := Nat.land v1531 v1932
    let v1934 := Nat.land v1702 v1933
    let v1935 := Nat.land v1702 v1934
    let v1936 := Nat.land v1897 v1935
    ∀ (P : Prop), (((v1905 = 1 ↔ v110 = 1 ∧ v1904 = 1)) → ((v1906 = 1 ↔ v270 = 1 ∧ v1905 = 1)) → ((v1907 = 1 ↔ v270 = 1 ∧ v1906 = 1)) → ((v1908 = 1 ↔ v13 = 1 ∧ v1907 = 1)) → ((v1909 = 1 ↔ v423 = 1 ∧ v1908 = 1)) → ((v1910 = 1 ↔ v471 = 1 ∧ v1909 = 1)) → ((v1911 = 1 ↔ v485 = 1 ∧ v1910 = 1)) → ((v1912 = 1 ↔ v593 = 1 ∧ v1911 = 1)) → ((v1913 = 1 ↔ v783 = 1 ∧ v1912 = 1)) → ((v1914 = 1 ↔ v1005 = 1 ∧ v1913 = 1)) → ((v1915 = 1 ↔ v1012 = 1 ∧ v1914 = 1)) → ((v1916 = 1 ↔ v1013 = 1 ∧ v1915 = 1)) → ((v1917 = 1 ↔ v1045 = 1 ∧ v1916 = 1)) → ((v1918 = 1 ↔ v1045 = 1 ∧ v1917 = 1)) → ((v1919 = 1 ↔ v1084 = 1 ∧ v1918 = 1)) → ((v1920 = 1 ↔ v13 = 1 ∧ v1919 = 1)) → ((v1921 = 1 ↔ v1139 = 1 ∧ v1920 = 1)) → ((v1922 = 1 ↔ v1187 = 1 ∧ v1921 = 1)) → ((v1923 = 1 ↔ v13 = 1 ∧ v1922 = 1)) → ((v1924 = 1 ↔ v110 = 1 ∧ v1923 = 1)) → ((v1925 = 1 ↔ v110 = 1 ∧ v1924 = 1)) → ((v1926 = 1 ↔ v1193 = 1 ∧ v1925 = 1)) → ((v1927 = 1 ↔ v1193 = 1 ∧ v1926 = 1)) → ((v1928 = 1 ↔ v13 = 1 ∧ v1927 = 1)) → ((v1929 = 1 ↔ v1351 = 1 ∧ v1928 = 1)) → ((v1930 = 1 ↔ v1397 = 1 ∧ v1929 = 1)) → ((v1931 = 1 ↔ v1417 = 1 ∧ v1930 = 1)) → ((v1932 = 1 ↔ v1531 = 1 ∧ v1931 = 1)) → ((v1933 = 1 ↔ v1531 = 1 ∧ v1932 = 1)) → ((v1934 = 1 ↔ v1702 = 1 ∧ v1933 = 1)) → ((v1935 = 1 ↔ v1702 = 1 ∧ v1934 = 1)) → ((v1936 = 1 ↔ v1897 = 1 ∧ v1935 = 1)) → P) → P := by
  intro v1905 v1906 v1907 v1908 v1909 v1910 v1911 v1912 v1913 v1914 v1915 v1916 v1917 v1918 v1919 v1920 v1921 v1922 v1923 v1924 v1925 v1926 v1927 v1928 v1929 v1930 v1931 v1932 v1933 v1934 v1935 v1936
  have hl : 0 < 1 := Nat.one_pos
  have h_v1905 : R 1 0 0 1 v1905 v1905 := (r_land hl h_v110 h_v1904 (of_decide_eq_true rfl))
  have e_v1905 : (v1905 = 1 ↔ v110 = 1 ∧ v1904 = 1) := e_land h_v110 h_v1904 (of_decide_eq_true rfl)
  have h_v1906 : R 1 0 0 1 v1906 v1906 := (r_land hl h_v270 h_v1905 (of_decide_eq_true rfl))
  have e_v1906 : (v1906 = 1 ↔ v270 = 1 ∧ v1905 = 1) := e_land h_v270 h_v1905 (of_decide_eq_true rfl)
  have h_v1907 : R 1 0 0 1 v1907 v1907 := (r_land hl h_v270 h_v1906 (of_decide_eq_true rfl))
  have e_v1907 : (v1907 = 1 ↔ v270 = 1 ∧ v1906 = 1) := e_land h_v270 h_v1906 (of_decide_eq_true rfl)
  have h_v1908 : R 1 0 0 1 v1908 v1908 := (r_land hl h_v13 h_v1907 (of_decide_eq_true rfl))
  have e_v1908 : (v1908 = 1 ↔ v13 = 1 ∧ v1907 = 1) := e_land h_v13 h_v1907 (of_decide_eq_true rfl)
  have h_v1909 : R 1 0 0 1 v1909 v1909 := (r_land hl h_v423 h_v1908 (of_decide_eq_true rfl))
  have e_v1909 : (v1909 = 1 ↔ v423 = 1 ∧ v1908 = 1) := e_land h_v423 h_v1908 (of_decide_eq_true rfl)
  have h_v1910 : R 1 0 0 1 v1910 v1910 := (r_land hl h_v471 h_v1909 (of_decide_eq_true rfl))
  have e_v1910 : (v1910 = 1 ↔ v471 = 1 ∧ v1909 = 1) := e_land h_v471 h_v1909 (of_decide_eq_true rfl)
  have h_v1911 : R 1 0 0 1 v1911 v1911 := (r_land hl h_v485 h_v1910 (of_decide_eq_true rfl))
  have e_v1911 : (v1911 = 1 ↔ v485 = 1 ∧ v1910 = 1) := e_land h_v485 h_v1910 (of_decide_eq_true rfl)
  have h_v1912 : R 1 0 0 1 v1912 v1912 := (r_land hl h_v593 h_v1911 (of_decide_eq_true rfl))
  have e_v1912 : (v1912 = 1 ↔ v593 = 1 ∧ v1911 = 1) := e_land h_v593 h_v1911 (of_decide_eq_true rfl)
  have h_v1913 : R 1 0 0 1 v1913 v1913 := (r_land hl h_v783 h_v1912 (of_decide_eq_true rfl))
  have e_v1913 : (v1913 = 1 ↔ v783 = 1 ∧ v1912 = 1) := e_land h_v783 h_v1912 (of_decide_eq_true rfl)
  have h_v1914 : R 1 0 0 1 v1914 v1914 := (r_land hl h_v1005 h_v1913 (of_decide_eq_true rfl))
  have e_v1914 : (v1914 = 1 ↔ v1005 = 1 ∧ v1913 = 1) := e_land h_v1005 h_v1913 (of_decide_eq_true rfl)
  have h_v1915 : R 1 0 0 1 v1915 v1915 := (r_land hl h_v1012 h_v1914 (of_decide_eq_true rfl))
  have e_v1915 : (v1915 = 1 ↔ v1012 = 1 ∧ v1914 = 1) := e_land h_v1012 h_v1914 (of_decide_eq_true rfl)
  have h_v1916 : R 1 0 0 1 v1916 v1916 := (r_land hl h_v1013 h_v1915 (of_decide_eq_true rfl))
  have e_v1916 : (v1916 = 1 ↔ v1013 = 1 ∧ v1915 = 1) := e_land h_v1013 h_v1915 (of_decide_eq_true rfl)
  have h_v1917 : R 1 0 0 1 v1917 v1917 := (r_land hl h_v1045 h_v1916 (of_decide_eq_true rfl))
  clear h_v1905 h_v1906 h_v1907 h_v1908 h_v1909 h_v1910 h_v1911 h_v1912 h_v1913 h_v1914 h_v1915
  have e_v1917 : (v1917 = 1 ↔ v1045 = 1 ∧ v1916 = 1) := e_land h_v1045 h_v1916 (of_decide_eq_true rfl)
  have h_v1918 : R 1 0 0 1 v1918 v1918 := (r_land hl h_v1045 h_v1917 (of_decide_eq_true rfl))
  have e_v1918 : (v1918 = 1 ↔ v1045 = 1 ∧ v1917 = 1) := e_land h_v1045 h_v1917 (of_decide_eq_true rfl)
  have h_v1919 : R 1 0 0 1 v1919 v1919 := (r_land hl h_v1084 h_v1918 (of_decide_eq_true rfl))
  have e_v1919 : (v1919 = 1 ↔ v1084 = 1 ∧ v1918 = 1) := e_land h_v1084 h_v1918 (of_decide_eq_true rfl)
  have h_v1920 : R 1 0 0 1 v1920 v1920 := (r_land hl h_v13 h_v1919 (of_decide_eq_true rfl))
  have e_v1920 : (v1920 = 1 ↔ v13 = 1 ∧ v1919 = 1) := e_land h_v13 h_v1919 (of_decide_eq_true rfl)
  have h_v1921 : R 1 0 0 1 v1921 v1921 := (r_land hl h_v1139 h_v1920 (of_decide_eq_true rfl))
  have e_v1921 : (v1921 = 1 ↔ v1139 = 1 ∧ v1920 = 1) := e_land h_v1139 h_v1920 (of_decide_eq_true rfl)
  have h_v1922 : R 1 0 0 1 v1922 v1922 := (r_land hl h_v1187 h_v1921 (of_decide_eq_true rfl))
  have e_v1922 : (v1922 = 1 ↔ v1187 = 1 ∧ v1921 = 1) := e_land h_v1187 h_v1921 (of_decide_eq_true rfl)
  have h_v1923 : R 1 0 0 1 v1923 v1923 := (r_land hl h_v13 h_v1922 (of_decide_eq_true rfl))
  have e_v1923 : (v1923 = 1 ↔ v13 = 1 ∧ v1922 = 1) := e_land h_v13 h_v1922 (of_decide_eq_true rfl)
  have h_v1924 : R 1 0 0 1 v1924 v1924 := (r_land hl h_v110 h_v1923 (of_decide_eq_true rfl))
  have e_v1924 : (v1924 = 1 ↔ v110 = 1 ∧ v1923 = 1) := e_land h_v110 h_v1923 (of_decide_eq_true rfl)
  have h_v1925 : R 1 0 0 1 v1925 v1925 := (r_land hl h_v110 h_v1924 (of_decide_eq_true rfl))
  have e_v1925 : (v1925 = 1 ↔ v110 = 1 ∧ v1924 = 1) := e_land h_v110 h_v1924 (of_decide_eq_true rfl)
  have h_v1926 : R 1 0 0 1 v1926 v1926 := (r_land hl h_v1193 h_v1925 (of_decide_eq_true rfl))
  have e_v1926 : (v1926 = 1 ↔ v1193 = 1 ∧ v1925 = 1) := e_land h_v1193 h_v1925 (of_decide_eq_true rfl)
  have h_v1927 : R 1 0 0 1 v1927 v1927 := (r_land hl h_v1193 h_v1926 (of_decide_eq_true rfl))
  have e_v1927 : (v1927 = 1 ↔ v1193 = 1 ∧ v1926 = 1) := e_land h_v1193 h_v1926 (of_decide_eq_true rfl)
  have h_v1928 : R 1 0 0 1 v1928 v1928 := (r_land hl h_v13 h_v1927 (of_decide_eq_true rfl))
  have e_v1928 : (v1928 = 1 ↔ v13 = 1 ∧ v1927 = 1) := e_land h_v13 h_v1927 (of_decide_eq_true rfl)
  have h_v1929 : R 1 0 0 1 v1929 v1929 := (r_land hl h_v1351 h_v1928 (of_decide_eq_true rfl))
  have e_v1929 : (v1929 = 1 ↔ v1351 = 1 ∧ v1928 = 1) := e_land h_v1351 h_v1928 (of_decide_eq_true rfl)
  clear h_v1916 h_v1917 h_v1918 h_v1919 h_v1920 h_v1921 h_v1922 h_v1923 h_v1924 h_v1925 h_v1926 h_v1927 h_v1928
  have h_v1930 : R 1 0 0 1 v1930 v1930 := (r_land hl h_v1397 h_v1929 (of_decide_eq_true rfl))
  have e_v1930 : (v1930 = 1 ↔ v1397 = 1 ∧ v1929 = 1) := e_land h_v1397 h_v1929 (of_decide_eq_true rfl)
  have h_v1931 : R 1 0 0 1 v1931 v1931 := (r_land hl h_v1417 h_v1930 (of_decide_eq_true rfl))
  have e_v1931 : (v1931 = 1 ↔ v1417 = 1 ∧ v1930 = 1) := e_land h_v1417 h_v1930 (of_decide_eq_true rfl)
  have h_v1932 : R 1 0 0 1 v1932 v1932 := (r_land hl h_v1531 h_v1931 (of_decide_eq_true rfl))
  have e_v1932 : (v1932 = 1 ↔ v1531 = 1 ∧ v1931 = 1) := e_land h_v1531 h_v1931 (of_decide_eq_true rfl)
  have h_v1933 : R 1 0 0 1 v1933 v1933 := (r_land hl h_v1531 h_v1932 (of_decide_eq_true rfl))
  have e_v1933 : (v1933 = 1 ↔ v1531 = 1 ∧ v1932 = 1) := e_land h_v1531 h_v1932 (of_decide_eq_true rfl)
  have h_v1934 : R 1 0 0 1 v1934 v1934 := (r_land hl h_v1702 h_v1933 (of_decide_eq_true rfl))
  have e_v1934 : (v1934 = 1 ↔ v1702 = 1 ∧ v1933 = 1) := e_land h_v1702 h_v1933 (of_decide_eq_true rfl)
  have h_v1935 : R 1 0 0 1 v1935 v1935 := (r_land hl h_v1702 h_v1934 (of_decide_eq_true rfl))
  have e_v1935 : (v1935 = 1 ↔ v1702 = 1 ∧ v1934 = 1) := e_land h_v1702 h_v1934 (of_decide_eq_true rfl)
  have h_v1936 : R 1 0 0 1 v1936 v1936 := (r_land hl h_v1897 h_v1935 (of_decide_eq_true rfl))
  have e_v1936 : (v1936 = 1 ↔ v1897 = 1 ∧ v1935 = 1) := e_land h_v1897 h_v1935 (of_decide_eq_true rfl)
  exact fun _ k => k e_v1905 e_v1906 e_v1907 e_v1908 e_v1909 e_v1910 e_v1911 e_v1912 e_v1913 e_v1914 e_v1915 e_v1916 e_v1917 e_v1918 e_v1919 e_v1920 e_v1921 e_v1922 e_v1923 e_v1924 e_v1925 e_v1926 e_v1927 e_v1928 e_v1929 e_v1930 e_v1931 e_v1932 e_v1933 e_v1934 e_v1935 e_v1936

end D3Prog
