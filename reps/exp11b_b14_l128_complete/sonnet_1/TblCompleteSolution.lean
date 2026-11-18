import Tbl
import TblLaws

open Tbl

namespace TblComplete

/-- The laws are complete: two rules that pass each law give the same answer for each case. -/
theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg c
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18, f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37, f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56, f57, f58, f59, f60, f61, f62, f63, f64, f65, f66, f67, f68, f69, f70, f71, f72, f73, f74, f75, f76, f77, f78, f79, f80, f81, f82, f83, f84, f85, f86, f87, f88, f89, f90, f91, f92, f93, f94, f95, f96, f97, f98, f99, f100, f101, f102, f103, f104, f105, f106, f107, f108, f109, f110, f111, f112, f113, f114, f115, f116, f117, f118, f119, f120, f121, f122, f123, f124, f125, f126, f127⟩ := hf
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, g35, g36, g37, g38, g39, g40, g41, g42, g43, g44, g45, g46, g47, g48, g49, g50, g51, g52, g53, g54, g55, g56, g57, g58, g59, g60, g61, g62, g63, g64, g65, g66, g67, g68, g69, g70, g71, g72, g73, g74, g75, g76, g77, g78, g79, g80, g81, g82, g83, g84, g85, g86, g87, g88, g89, g90, g91, g92, g93, g94, g95, g96, g97, g98, g99, g100, g101, g102, g103, g104, g105, g106, g107, g108, g109, g110, g111, g112, g113, g114, g115, g116, g117, g118, g119, g120, g121, g122, g123, g124, g125, g126, g127⟩ := hg
  cases hb13 : c.b13
  case false =>
    cases hb0 : c.b0
    case false =>
      cases hb2 : c.b2
      case false =>
        cases hb4 : c.b4
        case false =>
          cases hb7 : c.b7
          case false =>
            exact (f56 c ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g56 c ‹_› ‹_› ‹_› ‹_› ‹_›).symm
          case true =>
            cases hb5 : c.b5
            case false =>
              exact (f91 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g91 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
            case true =>
              exact (f54 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g54 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
        case true =>
          cases hb11 : c.b11
          case false =>
            cases hb12 : c.b12
            case false =>
              exact (f93 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g93 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
            case true =>
              exact (f84 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g84 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
          case true =>
            exact (f66 c ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g66 c ‹_› ‹_› ‹_› ‹_› ‹_›).symm
      case true =>
        cases hb1 : c.b1
        case false =>
          cases hb10 : c.b10
          case false =>
            cases hb9 : c.b9
            case false =>
              exact (f126 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g126 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
            case true =>
              exact (f65 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g65 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
          case true =>
            exact (f85 c ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g85 c ‹_› ‹_› ‹_› ‹_› ‹_›).symm
        case true =>
          cases hb5 : c.b5
          case false =>
            exact (f42 c ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g42 c ‹_› ‹_› ‹_› ‹_› ‹_›).symm
          case true =>
            cases hb6 : c.b6
            case false =>
              exact (f29 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g29 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
            case true =>
              exact (f11 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g11 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
    case true =>
      cases hb9 : c.b9
      case false =>
        cases hb10 : c.b10
        case false =>
          cases hb11 : c.b11
          case false =>
            cases hb6 : c.b6
            case false =>
              cases hb8 : c.b8
              case false =>
                cases hb3 : c.b3
                case false =>
                  cases hb5 : c.b5
                  case false =>
                    exact (f47 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g47 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    cases hb7 : c.b7
                    case false =>
                      exact (f63 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g63 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                    case true =>
                      exact (f81 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g81 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                case true =>
                  cases hb7 : c.b7
                  case false =>
                    exact (f77 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g77 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    exact (f6 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g6 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
              case true =>
                cases hb4 : c.b4
                case false =>
                  cases hb7 : c.b7
                  case false =>
                    exact (f60 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g60 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    exact (f2 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g2 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                case true =>
                  cases hb5 : c.b5
                  case false =>
                    exact (f3 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g3 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    exact (f70 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g70 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
            case true =>
              cases hb8 : c.b8
              case false =>
                cases hb4 : c.b4
                case false =>
                  exact (f110 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g110 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                case true =>
                  exact (f102 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g102 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
              case true =>
                exact (f113 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g113 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
          case true =>
            cases hb3 : c.b3
            case false =>
              cases hb6 : c.b6
              case false =>
                cases hb5 : c.b5
                case false =>
                  cases hb4 : c.b4
                  case false =>
                    cases hb12 : c.b12
                    case false =>
                      cases hb7 : c.b7
                      case false =>
                        cases hb1 : c.b1
                        case false =>
                          cases hb2 : c.b2
                          case false =>
                            cases hb8 : c.b8
                            case false =>
                              exact (f106 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g106 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                            case true =>
                              exact (f92 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g92 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                          case true =>
                            cases hb8 : c.b8
                            case false =>
                              exact (f69 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g69 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                            case true =>
                              exact (f0 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g0 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                        case true =>
                          cases hb2 : c.b2
                          case false =>
                            exact (f83 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g83 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                          case true =>
                            exact (f27 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g27 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                      case true =>
                        exact (f21 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g21 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                    case true =>
                      cases hb2 : c.b2
                      case false =>
                        exact (f25 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g25 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                      case true =>
                        exact (f116 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g116 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    exact (f8 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g8 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                case true =>
                  cases hb2 : c.b2
                  case false =>
                    cases hb4 : c.b4
                    case false =>
                      cases hb7 : c.b7
                      case false =>
                        exact (f46 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g46 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                      case true =>
                        cases hb1 : c.b1
                        case false =>
                          exact (f57 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g57 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                        case true =>
                          cases hb8 : c.b8
                          case false =>
                            cases hb12 : c.b12
                            case false =>
                              exact (f33 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g33 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                            case true =>
                              exact (f22 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g22 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                          case true =>
                            cases hb12 : c.b12
                            case false =>
                              exact (f62 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g62 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                            case true =>
                              exact (f97 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g97 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                    case true =>
                      cases hb7 : c.b7
                      case false =>
                        cases hb12 : c.b12
                        case false =>
                          exact (f37 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g37 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                        case true =>
                          cases hb8 : c.b8
                          case false =>
                            exact (f76 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g76 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                          case true =>
                            exact (f30 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g30 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                      case true =>
                        cases hb1 : c.b1
                        case false =>
                          exact (f13 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g13 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                        case true =>
                          cases hb12 : c.b12
                          case false =>
                            cases hb8 : c.b8
                            case false =>
                              exact (f96 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g96 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                            case true =>
                              exact (f35 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g35 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                          case true =>
                            cases hb8 : c.b8
                            case false =>
                              exact (f31 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g31 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                            case true =>
                              exact (f23 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g23 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    exact (f19 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g19 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
              case true =>
                cases hb7 : c.b7
                case false =>
                  cases hb12 : c.b12
                  case false =>
                    exact (f32 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g32 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    cases hb5 : c.b5
                    case false =>
                      exact (f68 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g68 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                    case true =>
                      exact (f107 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g107 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                case true =>
                  exact (f43 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g43 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
            case true =>
              cases hb5 : c.b5
              case false =>
                exact (f74 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g74 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
              case true =>
                cases hb4 : c.b4
                case false =>
                  exact (f94 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g94 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                case true =>
                  exact (f52 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g52 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
        case true =>
          cases hb3 : c.b3
          case false =>
            cases hb11 : c.b11
            case false =>
              exact (f87 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g87 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
            case true =>
              exact (f61 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g61 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
          case true =>
            exact (f75 c ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g75 c ‹_› ‹_› ‹_› ‹_› ‹_›).symm
      case true =>
        cases hb5 : c.b5
        case false =>
          cases hb12 : c.b12
          case false =>
            cases hb1 : c.b1
            case false =>
              cases hb4 : c.b4
              case false =>
                cases hb2 : c.b2
                case false =>
                  cases hb3 : c.b3
                  case false =>
                    cases hb7 : c.b7
                    case false =>
                      exact (f67 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g67 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                    case true =>
                      exact (f123 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g123 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    cases hb7 : c.b7
                    case false =>
                      exact (f82 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g82 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                    case true =>
                      cases hb8 : c.b8
                      case false =>
                        exact (f41 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g41 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                      case true =>
                        exact (f48 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g48 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                case true =>
                  cases hb3 : c.b3
                  case false =>
                    cases hb7 : c.b7
                    case false =>
                      cases hb10 : c.b10
                      case false =>
                        cases hb8 : c.b8
                        case false =>
                          exact (f58 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g58 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                        case true =>
                          exact (f71 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g71 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                      case true =>
                        exact (f95 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g95 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                    case true =>
                      cases hb11 : c.b11
                      case false =>
                        exact (f78 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g78 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                      case true =>
                        exact (f101 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g101 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    exact (f12 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g12 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
              case true =>
                exact (f5 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g5 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
            case true =>
              cases hb2 : c.b2
              case false =>
                exact (f55 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g55 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
              case true =>
                exact (f10 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g10 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
          case true =>
            cases hb4 : c.b4
            case false =>
              exact (f112 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g112 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
            case true =>
              cases hb11 : c.b11
              case false =>
                exact (f80 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g80 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
              case true =>
                exact (f88 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g88 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
        case true =>
          cases hb8 : c.b8
          case false =>
            cases hb4 : c.b4
            case false =>
              cases hb11 : c.b11
              case false =>
                cases hb7 : c.b7
                case false =>
                  exact (f64 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g64 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                case true =>
                  cases hb1 : c.b1
                  case false =>
                    cases hb12 : c.b12
                    case false =>
                      cases hb3 : c.b3
                      case false =>
                        exact (f90 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g90 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                      case true =>
                        cases hb6 : c.b6
                        case false =>
                          exact (f99 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g99 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                        case true =>
                          exact (f15 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g15 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                    case true =>
                      exact (f16 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g16 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    cases hb12 : c.b12
                    case false =>
                      exact (f111 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g111 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                    case true =>
                      exact (f4 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g4 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
              case true =>
                cases hb3 : c.b3
                case false =>
                  cases hb1 : c.b1
                  case false =>
                    cases hb2 : c.b2
                    case false =>
                      exact (f103 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g103 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                    case true =>
                      exact (f100 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g100 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    exact (f40 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g40 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                case true =>
                  cases hb1 : c.b1
                  case false =>
                    exact (f17 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g17 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    exact (f45 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g45 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
            case true =>
              cases hb12 : c.b12
              case false =>
                exact (f7 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g7 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
              case true =>
                exact (f49 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g49 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
          case true =>
            cases hb2 : c.b2
            case false =>
              exact (f115 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g115 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
            case true =>
              cases hb11 : c.b11
              case false =>
                cases hb10 : c.b10
                case false =>
                  cases hb3 : c.b3
                  case false =>
                    exact (f98 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g98 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    exact (f50 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g50 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                case true =>
                  cases hb4 : c.b4
                  case false =>
                    cases hb7 : c.b7
                    case false =>
                      cases hb6 : c.b6
                      case false =>
                        exact (f119 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g119 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                      case true =>
                        exact (f1 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g1 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                    case true =>
                      cases hb12 : c.b12
                      case false =>
                        cases hb6 : c.b6
                        case false =>
                          cases hb3 : c.b3
                          case false =>
                            exact (f79 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g79 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                          case true =>
                            exact (f104 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g104 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                        case true =>
                          exact (f105 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g105 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                      case true =>
                        exact (f120 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g120 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    cases hb6 : c.b6
                    case false =>
                      cases hb12 : c.b12
                      case false =>
                        cases hb7 : c.b7
                        case false =>
                          exact (f34 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g34 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                        case true =>
                          exact (f28 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g28 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                      case true =>
                        cases hb1 : c.b1
                        case false =>
                          cases hb3 : c.b3
                          case false =>
                            exact (f117 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g117 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                          case true =>
                            cases hb7 : c.b7
                            case false =>
                              exact (f20 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g20 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                            case true =>
                              exact (f89 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g89 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                        case true =>
                          cases hb7 : c.b7
                          case false =>
                            cases hb3 : c.b3
                            case false =>
                              exact (f53 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g53 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                            case true =>
                              exact (f127 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g127 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                          case true =>
                            cases hb3 : c.b3
                            case false =>
                              exact (f18 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g18 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                            case true =>
                              exact (f38 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g38 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                    case true =>
                      exact (f51 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g51 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
              case true =>
                cases hb10 : c.b10
                case false =>
                  cases hb7 : c.b7
                  case false =>
                    cases hb6 : c.b6
                    case false =>
                      cases hb3 : c.b3
                      case false =>
                        exact (f14 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g14 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                      case true =>
                        exact (f9 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g9 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                    case true =>
                      exact (f36 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g36 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    cases hb1 : c.b1
                    case false =>
                      exact (f108 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g108 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                    case true =>
                      cases hb6 : c.b6
                      case false =>
                        cases hb4 : c.b4
                        case false =>
                          exact (f118 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g118 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                        case true =>
                          cases hb3 : c.b3
                          case false =>
                            exact (f124 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g124 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                          case true =>
                            exact (f109 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g109 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                      case true =>
                        exact (f24 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g24 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                case true =>
                  cases hb7 : c.b7
                  case false =>
                    cases hb1 : c.b1
                    case false =>
                      cases hb4 : c.b4
                      case false =>
                        exact (f26 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g26 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                      case true =>
                        exact (f72 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g72 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                    case true =>
                      cases hb4 : c.b4
                      case false =>
                        exact (f114 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g114 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                      case true =>
                        exact (f86 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g86 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
                  case true =>
                    exact (f125 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g125 c ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›).symm
  case true =>
    cases hb5 : c.b5
    case false =>
      cases hb12 : c.b12
      case false =>
        cases hb8 : c.b8
        case false =>
          exact (f44 c ‹_› ‹_› ‹_› ‹_›).trans (g44 c ‹_› ‹_› ‹_› ‹_›).symm
        case true =>
          exact (f39 c ‹_› ‹_› ‹_› ‹_›).trans (g39 c ‹_› ‹_› ‹_› ‹_›).symm
      case true =>
        cases hb10 : c.b10
        case false =>
          cases hb2 : c.b2
          case false =>
            exact (f121 c ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g121 c ‹_› ‹_› ‹_› ‹_› ‹_›).symm
          case true =>
            exact (f122 c ‹_› ‹_› ‹_› ‹_› ‹_›).trans (g122 c ‹_› ‹_› ‹_› ‹_› ‹_›).symm
        case true =>
          exact (f73 c ‹_› ‹_› ‹_› ‹_›).trans (g73 c ‹_› ‹_› ‹_› ‹_›).symm
    case true =>
      exact (f59 c ‹_› ‹_›).trans (g59 c ‹_› ‹_›).symm

end TblComplete
