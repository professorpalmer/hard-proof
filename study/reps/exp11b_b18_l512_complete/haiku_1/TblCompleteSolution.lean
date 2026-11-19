/-
Hard Proof, experiment 11. Adversary solution for the completeness challenge.

The laws partition the 2^18 cases: each case lies in exactly one law's cube,
and no two laws disagree. So a rule that passes every law is fixed on every
case. The proof splits the cases along a decision tree derived from the law
cubes, then closes each leaf with the one law that covers it.
-/
import Tbl
import TblLaws

open Tbl

namespace TblComplete

set_option maxHeartbeats 4000000 in
/-- The laws are complete: two rules that pass each law give the same answer for each case. -/
theorem laws_complete : ∀ (f g : Decide), Passes f → Passes g → ∀ c : Case, f c = g c := by
  intro f g hf hg
  obtain ⟨⟨L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10, L11, L12, L13, L14, L15⟩, ⟨L16, L17, L18, L19, L20, L21, L22, L23, L24, L25, L26, L27, L28, L29, L30, L31⟩, ⟨L32, L33, L34, L35, L36, L37, L38, L39, L40, L41, L42, L43, L44, L45, L46, L47⟩, ⟨L48, L49, L50, L51, L52, L53, L54, L55, L56, L57, L58, L59, L60, L61, L62, L63⟩, ⟨L64, L65, L66, L67, L68, L69, L70, L71, L72, L73, L74, L75, L76, L77, L78, L79⟩, ⟨L80, L81, L82, L83, L84, L85, L86, L87, L88, L89, L90, L91, L92, L93, L94, L95⟩, ⟨L96, L97, L98, L99, L100, L101, L102, L103, L104, L105, L106, L107, L108, L109, L110, L111⟩, ⟨L112, L113, L114, L115, L116, L117, L118, L119, L120, L121, L122, L123, L124, L125, L126, L127⟩, ⟨L128, L129, L130, L131, L132, L133, L134, L135, L136, L137, L138, L139, L140, L141, L142, L143⟩, ⟨L144, L145, L146, L147, L148, L149, L150, L151, L152, L153, L154, L155, L156, L157, L158, L159⟩, ⟨L160, L161, L162, L163, L164, L165, L166, L167, L168, L169, L170, L171, L172, L173, L174, L175⟩, ⟨L176, L177, L178, L179, L180, L181, L182, L183, L184, L185, L186, L187, L188, L189, L190, L191⟩, ⟨L192, L193, L194, L195, L196, L197, L198, L199, L200, L201, L202, L203, L204, L205, L206, L207⟩, ⟨L208, L209, L210, L211, L212, L213, L214, L215, L216, L217, L218, L219, L220, L221, L222, L223⟩, ⟨L224, L225, L226, L227, L228, L229, L230, L231, L232, L233, L234, L235, L236, L237, L238, L239⟩, ⟨L240, L241, L242, L243, L244, L245, L246, L247, L248, L249, L250, L251, L252, L253, L254, L255⟩, ⟨L256, L257, L258, L259, L260, L261, L262, L263, L264, L265, L266, L267, L268, L269, L270, L271⟩, ⟨L272, L273, L274, L275, L276, L277, L278, L279, L280, L281, L282, L283, L284, L285, L286, L287⟩, ⟨L288, L289, L290, L291, L292, L293, L294, L295, L296, L297, L298, L299, L300, L301, L302, L303⟩, ⟨L304, L305, L306, L307, L308, L309, L310, L311, L312, L313, L314, L315, L316, L317, L318, L319⟩, ⟨L320, L321, L322, L323, L324, L325, L326, L327, L328, L329, L330, L331, L332, L333, L334, L335⟩, ⟨L336, L337, L338, L339, L340, L341, L342, L343, L344, L345, L346, L347, L348, L349, L350, L351⟩, ⟨L352, L353, L354, L355, L356, L357, L358, L359, L360, L361, L362, L363, L364, L365, L366, L367⟩, ⟨L368, L369, L370, L371, L372, L373, L374, L375, L376, L377, L378, L379, L380, L381, L382, L383⟩, ⟨L384, L385, L386, L387, L388, L389, L390, L391, L392, L393, L394, L395, L396, L397, L398, L399⟩, ⟨L400, L401, L402, L403, L404, L405, L406, L407, L408, L409, L410, L411, L412, L413, L414, L415⟩, ⟨L416, L417, L418, L419, L420, L421, L422, L423, L424, L425, L426, L427, L428, L429, L430, L431⟩, ⟨L432, L433, L434, L435, L436, L437, L438, L439, L440, L441, L442, L443, L444, L445, L446, L447⟩, ⟨L448, L449, L450, L451, L452, L453, L454, L455, L456, L457, L458, L459, L460, L461, L462, L463⟩, ⟨L464, L465, L466, L467, L468, L469, L470, L471, L472, L473, L474, L475, L476, L477, L478, L479⟩, ⟨L480, L481, L482, L483, L484, L485, L486, L487, L488, L489, L490, L491, L492, L493, L494, L495⟩, ⟨L496, L497, L498, L499, L500, L501, L502, L503, L504, L505, L506, L507, L508, L509, L510, L511⟩⟩ := hf
  obtain ⟨⟨M0, M1, M2, M3, M4, M5, M6, M7, M8, M9, M10, M11, M12, M13, M14, M15⟩, ⟨M16, M17, M18, M19, M20, M21, M22, M23, M24, M25, M26, M27, M28, M29, M30, M31⟩, ⟨M32, M33, M34, M35, M36, M37, M38, M39, M40, M41, M42, M43, M44, M45, M46, M47⟩, ⟨M48, M49, M50, M51, M52, M53, M54, M55, M56, M57, M58, M59, M60, M61, M62, M63⟩, ⟨M64, M65, M66, M67, M68, M69, M70, M71, M72, M73, M74, M75, M76, M77, M78, M79⟩, ⟨M80, M81, M82, M83, M84, M85, M86, M87, M88, M89, M90, M91, M92, M93, M94, M95⟩, ⟨M96, M97, M98, M99, M100, M101, M102, M103, M104, M105, M106, M107, M108, M109, M110, M111⟩, ⟨M112, M113, M114, M115, M116, M117, M118, M119, M120, M121, M122, M123, M124, M125, M126, M127⟩, ⟨M128, M129, M130, M131, M132, M133, M134, M135, M136, M137, M138, M139, M140, M141, M142, M143⟩, ⟨M144, M145, M146, M147, M148, M149, M150, M151, M152, M153, M154, M155, M156, M157, M158, M159⟩, ⟨M160, M161, M162, M163, M164, M165, M166, M167, M168, M169, M170, M171, M172, M173, M174, M175⟩, ⟨M176, M177, M178, M179, M180, M181, M182, M183, M184, M185, M186, M187, M188, M189, M190, M191⟩, ⟨M192, M193, M194, M195, M196, M197, M198, M199, M200, M201, M202, M203, M204, M205, M206, M207⟩, ⟨M208, M209, M210, M211, M212, M213, M214, M215, M216, M217, M218, M219, M220, M221, M222, M223⟩, ⟨M224, M225, M226, M227, M228, M229, M230, M231, M232, M233, M234, M235, M236, M237, M238, M239⟩, ⟨M240, M241, M242, M243, M244, M245, M246, M247, M248, M249, M250, M251, M252, M253, M254, M255⟩, ⟨M256, M257, M258, M259, M260, M261, M262, M263, M264, M265, M266, M267, M268, M269, M270, M271⟩, ⟨M272, M273, M274, M275, M276, M277, M278, M279, M280, M281, M282, M283, M284, M285, M286, M287⟩, ⟨M288, M289, M290, M291, M292, M293, M294, M295, M296, M297, M298, M299, M300, M301, M302, M303⟩, ⟨M304, M305, M306, M307, M308, M309, M310, M311, M312, M313, M314, M315, M316, M317, M318, M319⟩, ⟨M320, M321, M322, M323, M324, M325, M326, M327, M328, M329, M330, M331, M332, M333, M334, M335⟩, ⟨M336, M337, M338, M339, M340, M341, M342, M343, M344, M345, M346, M347, M348, M349, M350, M351⟩, ⟨M352, M353, M354, M355, M356, M357, M358, M359, M360, M361, M362, M363, M364, M365, M366, M367⟩, ⟨M368, M369, M370, M371, M372, M373, M374, M375, M376, M377, M378, M379, M380, M381, M382, M383⟩, ⟨M384, M385, M386, M387, M388, M389, M390, M391, M392, M393, M394, M395, M396, M397, M398, M399⟩, ⟨M400, M401, M402, M403, M404, M405, M406, M407, M408, M409, M410, M411, M412, M413, M414, M415⟩, ⟨M416, M417, M418, M419, M420, M421, M422, M423, M424, M425, M426, M427, M428, M429, M430, M431⟩, ⟨M432, M433, M434, M435, M436, M437, M438, M439, M440, M441, M442, M443, M444, M445, M446, M447⟩, ⟨M448, M449, M450, M451, M452, M453, M454, M455, M456, M457, M458, M459, M460, M461, M462, M463⟩, ⟨M464, M465, M466, M467, M468, M469, M470, M471, M472, M473, M474, M475, M476, M477, M478, M479⟩, ⟨M480, M481, M482, M483, M484, M485, M486, M487, M488, M489, M490, M491, M492, M493, M494, M495⟩, ⟨M496, M497, M498, M499, M500, M501, M502, M503, M504, M505, M506, M507, M508, M509, M510, M511⟩⟩ := hg
  intro c
  cases h1 : c.b1
  · cases h3 : c.b3
    · cases h7 : c.b7
      · cases h16 : c.b16
        · cases h6 : c.b6
          · cases h13 : c.b13
            · exact (L301 c h7 h1 h3 h6 h13 h16).trans (M301 c h7 h1 h3 h6 h13 h16).symm
            · cases h4 : c.b4
              · cases h17 : c.b17
                · exact (L427 c h16 h6 h1 h13 h7 h3 h17 h4).trans (M427 c h16 h6 h1 h13 h7 h3 h17 h4).symm
                · exact (L243 c h6 h4 h7 h13 h17 h3 h1 h16).trans (M243 c h6 h4 h7 h13 h17 h3 h1 h16).symm
              · exact (L396 c h3 h1 h4 h7 h13 h6 h16).trans (M396 c h3 h1 h4 h7 h13 h6 h16).symm
          · cases h9 : c.b9
            · cases h12 : c.b12
              · cases h0 : c.b0
                · exact (L130 c h3 h7 h0 h1 h9 h16 h12 h6).trans (M130 c h3 h7 h0 h1 h9 h16 h12 h6).symm
                · cases h11 : c.b11
                  · exact (L377 c h11 h1 h16 h7 h12 h0 h3 h9 h6).trans (M377 c h11 h1 h16 h7 h12 h0 h3 h9 h6).symm
                  · exact (L469 c h7 h1 h11 h0 h9 h6 h16 h3 h12).trans (M469 c h7 h1 h11 h0 h9 h6 h16 h3 h12).symm
              · cases h14 : c.b14
                · exact (L116 c h14 h9 h12 h1 h6 h7 h16 h3).trans (M116 c h14 h9 h12 h1 h6 h7 h16 h3).symm
                · exact (L284 c h6 h12 h3 h9 h16 h7 h1 h14).trans (M284 c h6 h12 h3 h9 h16 h7 h1 h14).symm
            · exact (L391 c h6 h7 h9 h16 h3 h1).trans (M391 c h6 h7 h9 h16 h3 h1).symm
        · cases h4 : c.b4
          · cases h5 : c.b5
            · cases h13 : c.b13
              · exact (L359 c h13 h7 h1 h4 h3 h16 h5).trans (M359 c h13 h7 h1 h4 h3 h16 h5).symm
              · exact (L49 c h16 h4 h1 h13 h3 h5 h7).trans (M49 c h16 h4 h1 h13 h3 h5 h7).symm
            · cases h15 : c.b15
              · cases h6 : c.b6
                · cases h12 : c.b12
                  · exact (L105 c h5 h6 h4 h15 h7 h12 h3 h1 h16).trans (M105 c h5 h6 h4 h15 h7 h12 h3 h1 h16).symm
                  · exact (L42 c h5 h7 h1 h16 h6 h4 h12 h3 h15).trans (M42 c h5 h7 h1 h16 h6 h4 h12 h3 h15).symm
                · exact (L415 c h1 h6 h4 h16 h5 h7 h3 h15).trans (M415 c h1 h6 h4 h16 h5 h7 h3 h15).symm
              · exact (L475 c h4 h5 h1 h7 h3 h15 h16).trans (M475 c h4 h5 h1 h7 h3 h15 h16).symm
          · cases h9 : c.b9
            · cases h12 : c.b12
              · exact (L109 c h9 h1 h7 h4 h3 h16 h12).trans (M109 c h9 h1 h7 h4 h3 h16 h12).symm
              · cases h11 : c.b11
                · exact (L460 c h4 h12 h3 h11 h16 h9 h1 h7).trans (M460 c h4 h12 h3 h11 h16 h9 h1 h7).symm
                · exact (L67 c h9 h12 h1 h16 h7 h4 h3 h11).trans (M67 c h9 h12 h1 h16 h7 h4 h3 h11).symm
            · cases h13 : c.b13
              · exact (L379 c h7 h13 h3 h9 h4 h1 h16).trans (M379 c h7 h13 h3 h9 h4 h1 h16).symm
              · cases h12 : c.b12
                · exact (L425 c h13 h3 h4 h1 h9 h16 h7 h12).trans (M425 c h13 h3 h4 h1 h9 h16 h7 h12).symm
                · exact (L1 c h13 h9 h4 h16 h12 h1 h7 h3).trans (M1 c h13 h9 h4 h16 h12 h1 h7 h3).symm
      · cases h8 : c.b8
        · exact (L437 c h1 h8 h7 h3).trans (M437 c h1 h8 h7 h3).symm
        · exact (L45 c h1 h7 h8 h3).trans (M45 c h1 h7 h8 h3).symm
    · cases h11 : c.b11
      · cases h16 : c.b16
        · cases h14 : c.b14
          · cases h9 : c.b9
            · cases h5 : c.b5
              · cases h4 : c.b4
                · cases h13 : c.b13
                  · exact (L342 c h5 h1 h4 h14 h3 h16 h9 h11 h13).trans (M342 c h5 h1 h4 h14 h3 h16 h9 h11 h13).symm
                  · exact (L510 c h3 h11 h5 h9 h16 h4 h13 h1 h14).trans (M510 c h3 h11 h5 h9 h16 h4 h13 h1 h14).symm
                · exact (L50 c h11 h14 h9 h4 h3 h16 h1 h5).trans (M50 c h11 h14 h9 h4 h3 h16 h1 h5).symm
              · cases h13 : c.b13
                · cases h7 : c.b7
                  · exact (L445 c h14 h11 h1 h9 h13 h5 h16 h7 h3).trans (M445 c h14 h11 h1 h9 h13 h5 h16 h7 h3).symm
                  · exact (L63 c h16 h1 h5 h7 h14 h9 h11 h3 h13).trans (M63 c h16 h1 h5 h7 h14 h9 h11 h3 h13).symm
                · exact (L435 c h13 h9 h1 h11 h16 h5 h3 h14).trans (M435 c h13 h9 h1 h11 h16 h5 h3 h14).symm
            · cases h15 : c.b15
              · exact (L298 c h14 h1 h16 h9 h15 h11 h3).trans (M298 c h14 h1 h16 h9 h15 h11 h3).symm
              · exact (L218 c h16 h3 h11 h9 h15 h14 h1).trans (M218 c h16 h3 h11 h9 h15 h14 h1).symm
          · exact (L266 c h16 h3 h1 h14 h11).trans (M266 c h16 h3 h1 h14 h11).symm
        · exact (L294 c h11 h3 h1 h16).trans (M294 c h11 h3 h1 h16).symm
      · cases h16 : c.b16
        · cases h14 : c.b14
          · exact (L258 c h1 h11 h16 h3 h14).trans (M258 c h1 h11 h16 h3 h14).symm
          · cases h5 : c.b5
            · exact (L462 c h11 h14 h5 h16 h3 h1).trans (M462 c h11 h14 h5 h16 h3 h1).symm
            · exact (L94 c h1 h11 h14 h5 h3 h16).trans (M94 c h1 h11 h14 h5 h3 h16).symm
        · cases h5 : c.b5
          · cases h17 : c.b17
            · exact (L286 c h11 h17 h5 h3 h16 h1).trans (M286 c h11 h17 h5 h3 h16 h1).symm
            · exact (L181 c h3 h5 h11 h16 h17 h1).trans (M181 c h3 h5 h11 h16 h17 h1).symm
          · cases h6 : c.b6
            · cases h7 : c.b7
              · exact (L238 c h16 h5 h11 h7 h1 h3 h6).trans (M238 c h16 h5 h11 h7 h1 h3 h6).symm
              · cases h0 : c.b0
                · exact (L182 c h6 h5 h1 h11 h16 h7 h3 h0).trans (M182 c h6 h5 h1 h11 h16 h7 h3 h0).symm
                · cases h2 : c.b2
                  · cases h8 : c.b8
                    · exact (L332 c h7 h0 h3 h16 h2 h5 h8 h6 h1 h11).trans (M332 c h7 h0 h3 h16 h2 h5 h8 h6 h1 h11).symm
                    · exact (L306 c h3 h5 h0 h1 h11 h2 h8 h16 h6 h7).trans (M306 c h3 h5 h0 h1 h11 h2 h8 h16 h6 h7).symm
                  · cases h8 : c.b8
                    · exact (L275 c h7 h6 h3 h11 h16 h1 h5 h2 h0 h8).trans (M275 c h7 h6 h3 h11 h16 h1 h5 h2 h0 h8).symm
                    · cases h4 : c.b4
                      · exact (L110 c h6 h2 h16 h8 h4 h5 h7 h0 h1 h11 h3).trans (M110 c h6 h2 h16 h8 h4 h5 h7 h0 h1 h11 h3).symm
                      · exact (L405 c h2 h6 h3 h1 h5 h11 h7 h4 h16 h8 h0).trans (M405 c h2 h6 h3 h1 h5 h11 h7 h4 h16 h8 h0).symm
            · exact (L201 c h11 h5 h6 h16 h1 h3).trans (M201 c h11 h5 h6 h16 h1 h3).symm
  · cases h0 : c.b0
    · cases h6 : c.b6
      · cases h12 : c.b12
        · cases h16 : c.b16
          · cases h4 : c.b4
            · exact (L158 c h16 h4 h12 h6 h1 h0).trans (M158 c h16 h4 h12 h6 h1 h0).symm
            · cases h14 : c.b14
              · exact (L29 c h14 h16 h0 h1 h12 h4 h6).trans (M29 c h14 h16 h0 h1 h12 h4 h6).symm
              · cases h11 : c.b11
                · exact (L36 c h1 h11 h0 h6 h16 h14 h12 h4).trans (M36 c h1 h11 h0 h6 h16 h14 h12 h4).symm
                · exact (L252 c h1 h0 h16 h14 h11 h6 h12 h4).trans (M252 c h1 h0 h16 h14 h11 h6 h12 h4).symm
          · cases h17 : c.b17
            · cases h15 : c.b15
              · exact (L159 c h15 h1 h17 h16 h12 h6 h0).trans (M159 c h15 h1 h17 h16 h12 h6 h0).symm
              · cases h9 : c.b9
                · cases h4 : c.b4
                  · cases h7 : c.b7
                    · exact (L76 c h16 h15 h4 h9 h1 h6 h7 h0 h12 h17).trans (M76 c h16 h15 h4 h9 h1 h6 h7 h0 h12 h17).symm
                    · exact (L268 c h4 h6 h17 h1 h0 h9 h12 h15 h16 h7).trans (M268 c h4 h6 h17 h1 h0 h9 h12 h15 h16 h7).symm
                  · exact (L433 c h12 h16 h0 h6 h4 h15 h9 h1 h17).trans (M433 c h12 h16 h0 h6 h4 h15 h9 h1 h17).symm
                · exact (L424 c h16 h9 h17 h12 h1 h15 h0 h6).trans (M424 c h16 h9 h17 h12 h1 h15 h0 h6).symm
            · cases h4 : c.b4
              · cases h11 : c.b11
                · exact (L247 c h11 h6 h12 h17 h16 h0 h4 h1).trans (M247 c h11 h6 h12 h17 h16 h0 h4 h1).symm
                · exact (L454 c h6 h4 h12 h17 h11 h0 h1 h16).trans (M454 c h6 h4 h12 h17 h11 h0 h1 h16).symm
              · exact (L222 c h12 h17 h6 h4 h1 h0 h16).trans (M222 c h12 h17 h6 h4 h1 h0 h16).symm
        · cases h7 : c.b7
          · cases h14 : c.b14
            · cases h16 : c.b16
              · cases h13 : c.b13
                · exact (L426 c h6 h14 h13 h7 h12 h0 h1 h16).trans (M426 c h6 h14 h13 h7 h12 h0 h1 h16).symm
                · exact (L333 c h1 h7 h13 h16 h12 h6 h14 h0).trans (M333 c h1 h7 h13 h16 h12 h6 h14 h0).symm
              · cases h8 : c.b8
                · cases h4 : c.b4
                  · exact (L51 c h0 h1 h16 h12 h6 h4 h7 h14 h8).trans (M51 c h0 h1 h16 h12 h6 h4 h7 h14 h8).symm
                  · cases h15 : c.b15
                    · exact (L449 c h16 h0 h14 h15 h12 h7 h8 h1 h6 h4).trans (M449 c h16 h0 h14 h15 h12 h7 h8 h1 h6 h4).symm
                    · exact (L423 c h8 h0 h16 h12 h6 h7 h1 h15 h14 h4).trans (M423 c h8 h0 h16 h12 h6 h7 h1 h15 h14 h4).symm
                · cases h2 : c.b2
                  · cases h9 : c.b9
                    · cases h17 : c.b17
                      · cases h5 : c.b5
                        · exact (L122 c h9 h16 h17 h5 h8 h2 h14 h7 h1 h6 h0 h12).trans (M122 c h9 h16 h17 h5 h8 h2 h14 h7 h1 h6 h0 h12).symm
                        · exact (L399 c h6 h14 h0 h2 h17 h1 h16 h5 h12 h7 h8 h9).trans (M399 c h6 h14 h0 h2 h17 h1 h16 h5 h12 h7 h8 h9).symm
                      · cases h15 : c.b15
                        · cases h5 : c.b5
                          · cases h10 : c.b10
                            · cases h3 : c.b3
                              · exact (L77 c h6 h12 h1 h15 h10 h0 h14 h7 h3 h17 h9 h2 h5 h16 h8).trans (M77 c h6 h12 h1 h15 h10 h0 h14 h7 h3 h17 h9 h2 h5 h16 h8).symm
                              · cases h11 : c.b11
                                · exact (L303 c h8 h9 h16 h2 h11 h6 h7 h5 h17 h12 h0 h15 h10 h14 h3 h1).trans (M303 c h8 h9 h16 h2 h11 h6 h7 h5 h17 h12 h0 h15 h10 h14 h3 h1).symm
                                · exact (L411 c h12 h10 h8 h11 h17 h1 h0 h2 h3 h9 h5 h7 h15 h14 h16 h6).trans (M411 c h12 h10 h8 h11 h17 h1 h0 h2 h3 h9 h5 h7 h15 h14 h16 h6).symm
                            · exact (L140 c h1 h15 h7 h17 h2 h0 h14 h8 h10 h12 h5 h16 h9 h6).trans (M140 c h1 h15 h7 h17 h2 h0 h14 h8 h10 h12 h5 h16 h9 h6).symm
                          · cases h3 : c.b3
                            · exact (L95 c h6 h1 h9 h15 h3 h5 h17 h16 h8 h2 h0 h7 h14 h12).trans (M95 c h6 h1 h9 h15 h3 h5 h17 h16 h8 h2 h0 h7 h14 h12).symm
                            · exact (L493 c h16 h3 h0 h7 h14 h5 h1 h8 h6 h12 h17 h9 h2 h15).trans (M493 c h16 h3 h0 h7 h14 h5 h1 h8 h6 h12 h17 h9 h2 h15).symm
                        · cases h4 : c.b4
                          · exact (L156 c h2 h1 h12 h8 h6 h4 h16 h15 h7 h14 h9 h0 h17).trans (M156 c h2 h1 h12 h8 h6 h4 h16 h15 h7 h14 h9 h0 h17).symm
                          · cases h13 : c.b13
                            · cases h11 : c.b11
                              · exact (L382 c h14 h16 h15 h6 h9 h4 h12 h11 h2 h8 h7 h17 h1 h0 h13).trans (M382 c h14 h16 h15 h6 h9 h4 h12 h11 h2 h8 h7 h17 h1 h0 h13).symm
                              · exact (L485 c h16 h4 h14 h12 h1 h8 h7 h17 h11 h9 h15 h0 h2 h13 h6).trans (M485 c h16 h4 h14 h12 h1 h8 h7 h17 h11 h9 h15 h0 h2 h13 h6).symm
                            · exact (L413 c h12 h9 h13 h2 h1 h15 h6 h14 h7 h17 h4 h16 h8 h0).trans (M413 c h12 h9 h13 h2 h1 h15 h6 h14 h7 h17 h4 h16 h8 h0).symm
                    · cases h10 : c.b10
                      · cases h17 : c.b17
                        · cases h11 : c.b11
                          · exact (L114 c h12 h9 h0 h8 h14 h16 h10 h11 h17 h6 h2 h1 h7).trans (M114 c h12 h9 h0 h8 h14 h16 h10 h11 h17 h6 h2 h1 h7).symm
                          · exact (L390 c h0 h2 h6 h12 h7 h1 h17 h11 h16 h8 h10 h9 h14).trans (M390 c h0 h2 h6 h12 h7 h1 h17 h11 h16 h8 h10 h9 h14).symm
                        · exact (L360 c h6 h10 h1 h9 h8 h2 h14 h0 h12 h16 h17 h7).trans (M360 c h6 h10 h1 h9 h8 h2 h14 h0 h12 h16 h17 h7).symm
                      · exact (L309 c h6 h10 h1 h12 h14 h2 h0 h8 h16 h7 h9).trans (M309 c h6 h10 h1 h12 h14 h2 h0 h8 h16 h7 h9).symm
                  · cases h17 : c.b17
                    · cases h4 : c.b4
                      · cases h15 : c.b15
                        · cases h9 : c.b9
                          · exact (L212 c h12 h15 h4 h8 h7 h0 h9 h2 h6 h16 h17 h1 h14).trans (M212 c h12 h15 h4 h8 h7 h0 h9 h2 h6 h16 h17 h1 h14).symm
                          · cases h3 : c.b3
                            · cases h11 : c.b11
                              · cases h13 : c.b13
                                · cases h10 : c.b10
                                  · exact (L345 c h17 h9 h4 h10 h3 h14 h12 h1 h7 h2 h15 h0 h6 h8 h13 h16 h11).trans (M345 c h17 h9 h4 h10 h3 h14 h12 h1 h7 h2 h15 h0 h6 h8 h13 h16 h11).symm
                                  · exact (L224 c h1 h13 h15 h11 h6 h10 h4 h7 h9 h8 h14 h0 h16 h17 h3 h12 h2).trans (M224 c h1 h13 h15 h11 h6 h10 h4 h7 h9 h8 h14 h0 h16 h17 h3 h12 h2).symm
                                · exact (L344 c h1 h9 h6 h13 h8 h17 h14 h3 h16 h11 h15 h7 h0 h2 h12 h4).trans (M344 c h1 h9 h6 h13 h8 h17 h14 h3 h16 h11 h15 h7 h0 h2 h12 h4).symm
                              · cases h10 : c.b10
                                · exact (L138 c h11 h1 h16 h7 h0 h17 h3 h2 h4 h15 h12 h8 h14 h9 h6 h10).trans (M138 c h11 h1 h16 h7 h0 h17 h3 h2 h4 h15 h12 h8 h14 h9 h6 h10).symm
                                · exact (L351 c h8 h1 h3 h16 h4 h6 h11 h17 h2 h15 h14 h12 h0 h9 h10 h7).trans (M351 c h8 h1 h3 h16 h4 h6 h11 h17 h2 h15 h14 h12 h0 h9 h10 h7).symm
                            · cases h5 : c.b5
                              · exact (L219 c h15 h17 h12 h3 h16 h14 h9 h0 h6 h5 h8 h2 h4 h7 h1).trans (M219 c h15 h17 h12 h3 h16 h14 h9 h0 h6 h5 h8 h2 h4 h7 h1).symm
                              · exact (L253 c h16 h3 h1 h0 h2 h8 h15 h4 h5 h9 h12 h14 h7 h6 h17).trans (M253 c h16 h3 h1 h0 h2 h8 h15 h4 h5 h9 h12 h14 h7 h6 h17).symm
                        · cases h13 : c.b13
                          · cases h10 : c.b10
                            · exact (L374 c h12 h0 h13 h2 h16 h8 h10 h4 h14 h15 h17 h6 h7 h1).trans (M374 c h12 h0 h13 h2 h16 h8 h10 h4 h14 h15 h17 h6 h7 h1).symm
                            · exact (L22 c h6 h4 h7 h2 h13 h0 h1 h17 h15 h10 h16 h12 h14 h8).trans (M22 c h6 h4 h7 h2 h13 h0 h1 h17 h15 h10 h16 h12 h14 h8).symm
                          · exact (L61 c h8 h15 h6 h7 h16 h14 h4 h12 h0 h17 h2 h13 h1).trans (M61 c h8 h15 h6 h7 h16 h14 h4 h12 h0 h17 h2 h13 h1).symm
                      · exact (L442 c h17 h6 h0 h16 h14 h12 h7 h1 h8 h4 h2).trans (M442 c h17 h6 h0 h16 h14 h12 h7 h1 h8 h4 h2).symm
                    · cases h11 : c.b11
                      · cases h13 : c.b13
                        · cases h4 : c.b4
                          · exact (L496 c h12 h6 h7 h2 h16 h14 h11 h0 h1 h13 h8 h17 h4).trans (M496 c h12 h6 h7 h2 h16 h14 h11 h0 h1 h13 h8 h17 h4).symm
                          · exact (L244 c h0 h12 h16 h1 h2 h8 h7 h6 h13 h14 h4 h11 h17).trans (M244 c h0 h12 h16 h1 h2 h8 h7 h6 h13 h14 h4 h11 h17).symm
                        · cases h10 : c.b10
                          · cases h9 : c.b9
                            · cases h4 : c.b4
                              · exact (L235 c h7 h0 h11 h2 h6 h4 h12 h16 h13 h9 h17 h1 h14 h8 h10).trans (M235 c h7 h0 h11 h2 h6 h4 h12 h16 h13 h9 h17 h1 h14 h8 h10).symm
                              · exact (L177 c h8 h2 h13 h4 h7 h12 h9 h11 h10 h0 h14 h16 h6 h17 h1).trans (M177 c h8 h2 h13 h4 h7 h12 h9 h11 h10 h0 h14 h16 h6 h17 h1).symm
                            · exact (L489 c h0 h8 h13 h14 h16 h11 h2 h17 h10 h1 h7 h6 h12 h9).trans (M489 c h0 h8 h13 h14 h16 h11 h2 h17 h10 h1 h7 h6 h12 h9).symm
                          · cases h3 : c.b3
                            · exact (L84 c h10 h17 h13 h2 h1 h6 h12 h3 h16 h0 h7 h14 h11 h8).trans (M84 c h10 h17 h13 h2 h1 h6 h12 h3 h16 h0 h7 h14 h11 h8).symm
                            · cases h9 : c.b9
                              · cases h5 : c.b5
                                · exact (L311 c h10 h2 h8 h13 h16 h0 h9 h17 h12 h5 h3 h11 h14 h7 h6 h1).trans (M311 c h10 h2 h8 h13 h16 h0 h9 h17 h12 h5 h3 h11 h14 h7 h6 h1).symm
                                · cases h4 : c.b4
                                  · exact (L463 c h8 h13 h17 h0 h7 h6 h3 h11 h2 h4 h9 h10 h1 h16 h14 h12 h5).trans (M463 c h8 h13 h17 h0 h7 h6 h3 h11 h2 h4 h9 h10 h1 h16 h14 h12 h5).symm
                                  · exact (L441 c h5 h0 h6 h3 h7 h12 h10 h11 h13 h8 h14 h1 h17 h4 h9 h2 h16).trans (M441 c h5 h0 h6 h3 h7 h12 h10 h11 h13 h8 h14 h1 h17 h4 h9 h2 h16).symm
                              · exact (L25 c h2 h0 h14 h13 h6 h11 h12 h8 h9 h7 h3 h10 h16 h1 h17).trans (M25 c h2 h0 h14 h13 h6 h11 h12 h8 h9 h7 h3 h10 h16 h1 h17).symm
                      · cases h10 : c.b10
                        · cases h13 : c.b13
                          · cases h5 : c.b5
                            · exact (L331 c h16 h14 h6 h10 h0 h7 h11 h5 h12 h1 h2 h13 h17 h8).trans (M331 c h16 h14 h6 h10 h0 h7 h11 h5 h12 h1 h2 h13 h17 h8).symm
                            · cases h9 : c.b9
                              · cases h3 : c.b3
                                · exact (L474 c h2 h16 h7 h12 h10 h1 h17 h6 h3 h0 h11 h5 h14 h9 h8 h13).trans (M474 c h2 h16 h7 h12 h10 h1 h17 h6 h3 h0 h11 h5 h14 h9 h8 h13).symm
                                · exact (L419 c h12 h6 h1 h5 h0 h16 h2 h3 h14 h7 h17 h9 h8 h13 h10 h11).trans (M419 c h12 h6 h1 h5 h0 h16 h2 h3 h14 h7 h17 h9 h8 h13 h10 h11).symm
                              · cases h15 : c.b15
                                · exact (L341 c h6 h17 h11 h1 h12 h2 h16 h13 h10 h0 h7 h5 h14 h9 h8 h15).trans (M341 c h6 h17 h11 h1 h12 h2 h16 h13 h10 h0 h7 h5 h14 h9 h8 h15).symm
                                · exact (L357 c h14 h6 h15 h11 h10 h13 h1 h16 h17 h2 h9 h12 h8 h0 h5 h7).trans (M357 c h14 h6 h15 h11 h10 h13 h1 h16 h17 h2 h9 h12 h8 h0 h5 h7).symm
                          · exact (L189 c h16 h12 h14 h8 h17 h6 h1 h10 h0 h13 h7 h11 h2).trans (M189 c h16 h12 h14 h8 h17 h6 h1 h10 h0 h13 h7 h11 h2).symm
                        · cases h13 : c.b13
                          · cases h5 : c.b5
                            · cases h9 : c.b9
                              · exact (L368 c h7 h13 h2 h1 h6 h5 h17 h14 h12 h16 h9 h0 h11 h8 h10).trans (M368 c h7 h13 h2 h1 h6 h5 h17 h14 h12 h16 h9 h0 h11 h8 h10).symm
                              · exact (L319 c h12 h9 h6 h0 h10 h14 h16 h2 h5 h11 h17 h8 h1 h13 h7).trans (M319 c h12 h9 h6 h0 h10 h14 h16 h2 h5 h11 h17 h8 h1 h13 h7).symm
                            · exact (L225 c h11 h17 h7 h1 h2 h10 h8 h13 h6 h0 h14 h16 h5 h12).trans (M225 c h11 h17 h7 h1 h2 h10 h8 h13 h6 h0 h14 h16 h5 h12).symm
                          · cases h4 : c.b4
                            · exact (L323 c h1 h6 h7 h17 h16 h13 h2 h10 h0 h4 h14 h12 h8 h11).trans (M323 c h1 h6 h7 h17 h16 h13 h2 h10 h0 h4 h14 h12 h8 h11).symm
                            · exact (L451 c h12 h13 h6 h14 h4 h16 h8 h10 h7 h2 h17 h11 h1 h0).trans (M451 c h12 h13 h6 h14 h4 h16 h8 h10 h7 h2 h17 h11 h1 h0).symm
            · cases h10 : c.b10
              · cases h3 : c.b3
                · exact (L420 c h6 h0 h14 h12 h1 h7 h10 h3).trans (M420 c h6 h0 h14 h12 h1 h7 h10 h3).symm
                · exact (L184 c h6 h10 h1 h7 h3 h14 h12 h0).trans (M184 c h6 h10 h1 h7 h3 h14 h12 h0).symm
              · cases h17 : c.b17
                · exact (L459 c h1 h12 h0 h14 h17 h6 h7 h10).trans (M459 c h1 h12 h0 h14 h17 h6 h7 h10).symm
                · cases h5 : c.b5
                  · cases h8 : c.b8
                    · cases h13 : c.b13
                      · cases h3 : c.b3
                        · cases h9 : c.b9
                          · exact (L378 c h8 h0 h7 h13 h10 h3 h17 h6 h1 h12 h5 h9 h14).trans (M378 c h8 h0 h7 h13 h10 h3 h17 h6 h1 h12 h5 h9 h14).symm
                          · cases h15 : c.b15
                            · exact (L55 c h12 h9 h14 h15 h17 h7 h6 h0 h5 h1 h3 h13 h10 h8).trans (M55 c h12 h9 h14 h15 h17 h7 h6 h0 h5 h1 h3 h13 h10 h8).symm
                            · exact (L2 c h9 h0 h3 h1 h14 h6 h17 h15 h5 h13 h7 h8 h12 h10).trans (M2 c h9 h0 h3 h1 h14 h6 h17 h15 h5 h13 h7 h8 h12 h10).symm
                        · exact (L314 c h13 h8 h1 h14 h0 h3 h17 h12 h7 h6 h5 h10).trans (M314 c h13 h8 h1 h14 h0 h3 h17 h12 h7 h6 h5 h10).symm
                      · cases h4 : c.b4
                        · exact (L343 c h4 h10 h7 h5 h0 h12 h13 h8 h6 h1 h17 h14).trans (M343 c h4 h10 h7 h5 h0 h12 h13 h8 h6 h1 h17 h14).symm
                        · exact (L292 c h6 h17 h5 h14 h1 h7 h0 h8 h13 h10 h4 h12).trans (M292 c h6 h17 h5 h14 h1 h7 h0 h8 h13 h10 h4 h12).symm
                    · cases h13 : c.b13
                      · exact (L186 c h8 h0 h14 h13 h1 h17 h5 h10 h12 h6 h7).trans (M186 c h8 h0 h14 h13 h1 h17 h5 h10 h12 h6 h7).symm
                      · exact (L409 c h6 h17 h5 h13 h1 h14 h7 h10 h12 h8 h0).trans (M409 c h6 h17 h5 h13 h1 h14 h7 h10 h12 h8 h0).symm
                  · cases h8 : c.b8
                    · exact (L85 c h17 h1 h8 h7 h6 h0 h5 h12 h14 h10).trans (M85 c h17 h1 h8 h7 h6 h0 h5 h12 h14 h10).symm
                    · cases h4 : c.b4
                      · exact (L124 c h17 h10 h8 h7 h4 h0 h6 h1 h12 h5 h14).trans (M124 c h17 h10 h8 h7 h4 h0 h6 h1 h12 h5 h14).symm
                      · exact (L64 c h14 h7 h0 h4 h12 h1 h17 h8 h10 h6 h5).trans (M64 c h14 h7 h0 h4 h12 h1 h17 h8 h10 h6 h5).symm
          · cases h17 : c.b17
            · cases h10 : c.b10
              · cases h11 : c.b11
                · cases h2 : c.b2
                  · cases h9 : c.b9
                    · cases h13 : c.b13
                      · cases h15 : c.b15
                        · cases h16 : c.b16
                          · cases h8 : c.b8
                            · cases h5 : c.b5
                              · exact (L68 c h12 h0 h11 h1 h8 h6 h10 h17 h7 h9 h16 h15 h13 h2 h5).trans (M68 c h12 h0 h11 h1 h8 h6 h10 h17 h7 h9 h16 h15 h13 h2 h5).symm
                              · exact (L166 c h5 h0 h12 h9 h15 h17 h13 h11 h6 h16 h8 h1 h10 h2 h7).trans (M166 c h5 h0 h12 h9 h15 h17 h13 h11 h6 h16 h8 h1 h10 h2 h7).symm
                            · exact (L239 c h15 h10 h1 h2 h6 h11 h16 h13 h9 h0 h12 h8 h17 h7).trans (M239 c h15 h10 h1 h2 h6 h11 h16 h13 h9 h0 h12 h8 h17 h7).symm
                          · exact (L499 c h12 h9 h6 h1 h11 h0 h17 h7 h15 h16 h2 h10 h13).trans (M499 c h12 h9 h6 h1 h11 h0 h17 h7 h15 h16 h2 h10 h13).symm
                        · cases h16 : c.b16
                          · exact (L78 c h15 h16 h7 h10 h11 h17 h13 h12 h2 h9 h1 h0 h6).trans (M78 c h15 h16 h7 h10 h11 h17 h13 h12 h2 h9 h1 h0 h6).symm
                          · exact (L20 c h16 h17 h1 h13 h10 h9 h0 h2 h6 h15 h11 h12 h7).trans (M20 c h16 h17 h1 h13 h10 h9 h0 h2 h6 h15 h11 h12 h7).symm
                      · exact (L123 c h11 h6 h7 h17 h12 h2 h1 h13 h0 h10 h9).trans (M123 c h11 h6 h7 h17 h12 h2 h1 h13 h0 h10 h9).symm
                    · cases h15 : c.b15
                      · exact (L131 c h11 h2 h10 h6 h0 h15 h12 h1 h17 h7 h9).trans (M131 c h11 h2 h10 h6 h0 h15 h12 h1 h17 h7 h9).symm
                      · cases h13 : c.b13
                        · cases h8 : c.b8
                          · cases h3 : c.b3
                            · exact (L229 c h17 h15 h7 h6 h2 h3 h12 h8 h1 h10 h9 h13 h0 h11).trans (M229 c h17 h15 h7 h6 h2 h3 h12 h8 h1 h10 h9 h13 h0 h11).symm
                            · exact (L139 c h2 h9 h10 h3 h13 h6 h11 h1 h12 h17 h0 h8 h7 h15).trans (M139 c h2 h9 h10 h3 h13 h6 h11 h1 h12 h17 h0 h8 h7 h15).symm
                          · cases h16 : c.b16
                            · cases h14 : c.b14
                              · exact (L3 c h10 h8 h9 h2 h6 h13 h17 h14 h1 h16 h11 h7 h0 h12 h15).trans (M3 c h10 h8 h9 h2 h6 h13 h17 h14 h1 h16 h11 h7 h0 h12 h15).symm
                              · cases h3 : c.b3
                                · exact (L87 c h14 h16 h0 h3 h15 h8 h13 h17 h1 h12 h10 h9 h2 h7 h6 h11).trans (M87 c h14 h16 h0 h3 h15 h8 h13 h17 h1 h12 h10 h9 h2 h7 h6 h11).symm
                                · exact (L192 c h0 h10 h16 h7 h17 h8 h15 h2 h12 h13 h6 h3 h9 h14 h11 h1).trans (M192 c h0 h10 h16 h7 h17 h8 h15 h2 h12 h13 h6 h3 h9 h14 h11 h1).symm
                            · exact (L211 c h9 h13 h1 h17 h15 h7 h11 h16 h8 h6 h12 h0 h10 h2).trans (M211 c h9 h13 h1 h17 h15 h7 h11 h16 h8 h6 h12 h0 h10 h2).symm
                        · cases h5 : c.b5
                          · exact (L146 c h15 h13 h9 h0 h7 h6 h5 h2 h17 h11 h10 h12 h1).trans (M146 c h15 h13 h9 h0 h7 h6 h5 h2 h17 h11 h10 h12 h1).symm
                          · exact (L362 c h12 h0 h13 h6 h10 h5 h7 h15 h1 h17 h2 h11 h9).trans (M362 c h12 h0 h13 h6 h10 h5 h7 h15 h1 h17 h2 h11 h9).symm
                  · exact (L108 c h10 h1 h2 h6 h0 h11 h17 h7 h12).trans (M108 c h10 h1 h2 h6 h0 h11 h17 h7 h12).symm
                · cases h16 : c.b16
                  · cases h2 : c.b2
                    · exact (L448 c h0 h16 h6 h1 h17 h7 h11 h10 h2 h12).trans (M448 c h0 h16 h6 h1 h17 h7 h11 h10 h2 h12).symm
                    · exact (L142 c h2 h10 h6 h16 h11 h7 h17 h12 h0 h1).trans (M142 c h2 h10 h6 h16 h11 h7 h17 h12 h0 h1).symm
                  · cases h8 : c.b8
                    · cases h15 : c.b15
                      · exact (L388 c h1 h0 h8 h15 h12 h6 h16 h11 h17 h7 h10).trans (M388 c h1 h0 h8 h15 h12 h6 h16 h11 h17 h7 h10).symm
                      · exact (L143 c h11 h12 h8 h1 h15 h6 h0 h7 h16 h10 h17).trans (M143 c h11 h12 h8 h1 h15 h6 h0 h7 h16 h10 h17).symm
                    · cases h3 : c.b3
                      · cases h2 : c.b2
                        · exact (L91 c h1 h8 h3 h16 h2 h11 h6 h10 h17 h0 h7 h12).trans (M91 c h1 h8 h3 h16 h2 h11 h6 h10 h17 h0 h7 h12).symm
                        · exact (L265 c h6 h10 h11 h3 h1 h8 h2 h12 h16 h17 h7 h0).trans (M265 c h6 h10 h11 h3 h1 h8 h2 h12 h16 h17 h7 h0).symm
                      · exact (L214 c h11 h1 h0 h3 h17 h6 h16 h8 h12 h7 h10).trans (M214 c h11 h1 h0 h3 h17 h6 h16 h8 h12 h7 h10).symm
              · cases h3 : c.b3
                · cases h16 : c.b16
                  · cases h9 : c.b9
                    · cases h11 : c.b11
                      · cases h8 : c.b8
                        · exact (L57 c h10 h7 h16 h17 h3 h11 h12 h0 h8 h1 h9 h6).trans (M57 c h10 h7 h16 h17 h3 h11 h12 h0 h8 h1 h9 h6).symm
                        · cases h14 : c.b14
                          · cases h5 : c.b5
                            · cases h15 : c.b15
                              · exact (L261 c h15 h14 h11 h0 h17 h10 h3 h7 h1 h9 h5 h16 h6 h12 h8).trans (M261 c h15 h14 h11 h0 h17 h10 h3 h7 h1 h9 h5 h16 h6 h12 h8).symm
                              · exact (L431 c h0 h6 h12 h15 h16 h17 h1 h10 h9 h3 h8 h7 h11 h5 h14).trans (M431 c h0 h6 h12 h15 h16 h17 h1 h10 h9 h3 h8 h7 h11 h5 h14).symm
                            · cases h4 : c.b4
                              · exact (L337 c h11 h6 h7 h8 h3 h5 h0 h14 h17 h10 h16 h1 h12 h4 h9).trans (M337 c h11 h6 h7 h8 h3 h5 h0 h14 h17 h10 h16 h1 h12 h4 h9).symm
                              · cases h13 : c.b13
                                · cases h15 : c.b15
                                  · exact (L148 c h10 h12 h1 h6 h9 h3 h17 h16 h13 h14 h0 h11 h15 h7 h5 h8 h4).trans (M148 c h10 h12 h1 h6 h9 h3 h17 h16 h13 h14 h0 h11 h15 h7 h5 h8 h4).symm
                                  · exact (L348 c h9 h7 h1 h6 h16 h13 h11 h15 h14 h12 h0 h3 h17 h10 h5 h8 h4).trans (M348 c h9 h7 h1 h6 h16 h13 h11 h15 h14 h12 h0 h3 h17 h10 h5 h8 h4).symm
                                · cases h15 : c.b15
                                  · exact (L327 c h12 h17 h7 h4 h6 h9 h14 h10 h16 h5 h0 h11 h1 h8 h15 h3 h13).trans (M327 c h12 h17 h7 h4 h6 h9 h14 h10 h16 h5 h0 h11 h1 h8 h15 h3 h13).symm
                                  · exact (L410 c h16 h5 h1 h13 h8 h10 h11 h12 h3 h6 h15 h14 h17 h7 h4 h9 h0).trans (M410 c h16 h5 h1 h13 h8 h10 h11 h12 h3 h6 h15 h14 h17 h7 h4 h9 h0).symm
                          · exact (L19 c h6 h3 h12 h17 h11 h1 h14 h9 h8 h7 h10 h16 h0).trans (M19 c h6 h3 h12 h17 h11 h1 h14 h9 h8 h7 h10 h16 h0).symm
                      · cases h13 : c.b13
                        · cases h14 : c.b14
                          · exact (L269 c h9 h0 h16 h10 h12 h13 h14 h6 h17 h11 h1 h7 h3).trans (M269 c h9 h0 h16 h10 h12 h13 h14 h6 h17 h11 h1 h7 h3).symm
                          · exact (L202 c h6 h11 h17 h0 h16 h10 h14 h3 h1 h7 h13 h12 h9).trans (M202 c h6 h11 h17 h0 h16 h10 h14 h3 h1 h7 h13 h12 h9).symm
                        · cases h14 : c.b14
                          · cases h15 : c.b15
                            · exact (L304 c h9 h14 h10 h7 h17 h6 h3 h0 h16 h1 h13 h15 h11 h12).trans (M304 c h9 h14 h10 h7 h17 h6 h3 h0 h16 h1 h13 h15 h11 h12).symm
                            · cases h4 : c.b4
                              · exact (L392 c h14 h9 h10 h0 h1 h11 h6 h17 h4 h7 h15 h3 h13 h12 h16).trans (M392 c h14 h9 h10 h0 h1 h11 h6 h17 h4 h7 h15 h3 h13 h12 h16).symm
                              · exact (L54 c h7 h14 h6 h17 h15 h13 h1 h16 h4 h12 h10 h3 h0 h9 h11).trans (M54 c h7 h14 h6 h17 h15 h13 h1 h16 h4 h12 h10 h3 h0 h9 h11).symm
                          · cases h15 : c.b15
                            · cases h2 : c.b2
                              · exact (L43 c h11 h3 h0 h1 h14 h17 h13 h7 h9 h12 h15 h2 h16 h6 h10).trans (M43 c h11 h3 h0 h1 h14 h17 h13 h7 h9 h12 h15 h2 h16 h6 h10).symm
                              · cases h5 : c.b5
                                · exact (L480 c h0 h7 h2 h1 h16 h5 h6 h10 h9 h3 h11 h17 h15 h13 h14 h12).trans (M480 c h0 h7 h2 h1 h16 h5 h6 h10 h9 h3 h11 h17 h15 h13 h14 h12).symm
                                · exact (L444 c h13 h16 h14 h11 h2 h3 h15 h5 h7 h17 h6 h0 h1 h9 h12 h10).trans (M444 c h13 h16 h14 h11 h2 h3 h15 h5 h7 h17 h6 h0 h1 h9 h12 h10).symm
                            · cases h5 : c.b5
                              · exact (L162 c h16 h10 h7 h9 h12 h14 h3 h11 h1 h17 h5 h13 h15 h0 h6).trans (M162 c h16 h10 h7 h9 h12 h14 h3 h11 h1 h17 h5 h13 h15 h0 h6).symm
                              · cases h4 : c.b4
                                · exact (L185 c h3 h16 h14 h0 h5 h9 h13 h6 h17 h11 h4 h15 h10 h1 h7 h12).trans (M185 c h3 h16 h14 h0 h5 h9 h13 h6 h17 h11 h4 h15 h10 h1 h7 h12).symm
                                · cases h8 : c.b8
                                  · cases h2 : c.b2
                                    · exact (L479 c h7 h1 h14 h11 h2 h6 h12 h10 h4 h15 h0 h13 h5 h8 h16 h3 h9 h17).trans (M479 c h7 h1 h14 h11 h2 h6 h12 h10 h4 h15 h0 h13 h5 h8 h16 h3 h9 h17).symm
                                    · exact (L369 c h2 h17 h16 h4 h12 h3 h5 h7 h10 h15 h14 h13 h6 h1 h8 h11 h9 h0).trans (M369 c h2 h17 h16 h4 h12 h3 h5 h7 h10 h15 h14 h13 h6 h1 h8 h11 h9 h0).symm
                                  · exact (L102 c h3 h10 h13 h16 h0 h12 h17 h5 h6 h8 h9 h14 h1 h7 h15 h11 h4).trans (M102 c h3 h10 h13 h16 h0 h12 h17 h5 h6 h8 h9 h14 h1 h7 h15 h11 h4).symm
                    · cases h11 : c.b11
                      · cases h8 : c.b8
                        · cases h13 : c.b13
                          · cases h5 : c.b5
                            · exact (L355 c h9 h0 h7 h16 h17 h10 h3 h12 h11 h13 h6 h8 h5 h1).trans (M355 c h9 h0 h7 h16 h17 h10 h3 h12 h11 h13 h6 h8 h5 h1).symm
                            · exact (L160 c h9 h0 h8 h12 h17 h6 h10 h5 h16 h11 h3 h7 h13 h1).trans (M160 c h9 h0 h8 h12 h17 h6 h10 h5 h16 h11 h3 h7 h13 h1).symm
                          · cases h15 : c.b15
                            · cases h2 : c.b2
                              · exact (L40 c h2 h1 h9 h12 h10 h7 h16 h0 h8 h3 h15 h13 h17 h6 h11).trans (M40 c h2 h1 h9 h12 h10 h7 h16 h0 h8 h3 h15 h13 h17 h6 h11).symm
                              · exact (L394 c h2 h3 h8 h13 h7 h1 h16 h9 h6 h15 h10 h12 h0 h11 h17).trans (M394 c h2 h3 h8 h13 h7 h1 h16 h9 h6 h15 h10 h12 h0 h11 h17).symm
                            · exact (L115 c h17 h11 h0 h13 h9 h12 h16 h15 h8 h7 h3 h1 h6 h10).trans (M115 c h17 h11 h0 h13 h9 h12 h16 h15 h8 h7 h3 h1 h6 h10).symm
                        · exact (L188 c h3 h11 h16 h12 h1 h7 h8 h6 h10 h9 h17 h0).trans (M188 c h3 h11 h16 h12 h1 h7 h8 h6 h10 h9 h17 h0).symm
                      · cases h4 : c.b4
                        · cases h5 : c.b5
                          · exact (L321 c h0 h4 h16 h6 h5 h7 h10 h12 h11 h17 h1 h9 h3).trans (M321 c h0 h4 h16 h6 h5 h7 h10 h12 h11 h17 h1 h9 h3).symm
                          · exact (L245 c h4 h7 h1 h11 h0 h12 h3 h16 h10 h9 h6 h5 h17).trans (M245 c h4 h7 h1 h11 h0 h12 h3 h16 h10 h9 h6 h5 h17).symm
                        · cases h5 : c.b5
                          · exact (L90 c h6 h0 h7 h12 h9 h17 h11 h5 h1 h3 h10 h4 h16).trans (M90 c h6 h0 h7 h12 h9 h17 h11 h5 h1 h3 h10 h4 h16).symm
                          · exact (L121 c h9 h3 h10 h16 h6 h1 h11 h5 h4 h12 h7 h0 h17).trans (M121 c h9 h3 h10 h16 h6 h1 h11 h5 h4 h12 h7 h0 h17).symm
                  · cases h5 : c.b5
                    · cases h8 : c.b8
                      · cases h4 : c.b4
                        · cases h14 : c.b14
                          · exact (L174 c h4 h1 h10 h17 h5 h3 h6 h14 h8 h16 h7 h0 h12).trans (M174 c h4 h1 h10 h17 h5 h3 h6 h14 h8 h16 h7 h0 h12).symm
                          · exact (L127 c h4 h5 h12 h8 h6 h17 h16 h3 h10 h1 h0 h7 h14).trans (M127 c h4 h5 h12 h8 h6 h17 h16 h3 h10 h1 h0 h7 h14).symm
                        · exact (L172 c h1 h0 h5 h7 h8 h10 h12 h16 h6 h17 h3 h4).trans (M172 c h1 h0 h5 h7 h8 h10 h12 h16 h6 h17 h3 h4).symm
                      · cases h9 : c.b9
                        · cases h15 : c.b15
                          · cases h13 : c.b13
                            · cases h2 : c.b2
                              · exact (L221 c h9 h15 h13 h7 h12 h5 h17 h10 h6 h8 h2 h1 h3 h16 h0).trans (M221 c h9 h15 h13 h7 h12 h5 h17 h10 h6 h8 h2 h1 h3 h16 h0).symm
                              · exact (L271 c h0 h13 h12 h15 h2 h9 h7 h6 h8 h5 h1 h17 h3 h16 h10).trans (M271 c h0 h13 h12 h15 h2 h9 h7 h6 h8 h5 h1 h17 h3 h16 h10).symm
                            · exact (L370 c h13 h6 h7 h9 h12 h15 h8 h17 h0 h10 h16 h1 h5 h3).trans (M370 c h13 h6 h7 h9 h12 h15 h8 h17 h0 h10 h16 h1 h5 h3).symm
                          · cases h11 : c.b11
                            · exact (L86 c h1 h10 h0 h15 h12 h8 h17 h7 h3 h5 h16 h6 h11 h9).trans (M86 c h1 h10 h0 h15 h12 h8 h17 h7 h3 h5 h16 h6 h11 h9).symm
                            · exact (L100 c h1 h17 h11 h9 h16 h0 h3 h10 h7 h12 h15 h8 h5 h6).trans (M100 c h1 h17 h11 h9 h16 h0 h3 h10 h7 h12 h15 h8 h5 h6).symm
                        · cases h4 : c.b4
                          · cases h14 : c.b14
                            · exact (L157 c h1 h16 h10 h6 h0 h9 h5 h8 h7 h4 h14 h12 h17 h3).trans (M157 c h1 h16 h10 h6 h0 h9 h5 h8 h7 h4 h14 h12 h17 h3).symm
                            · exact (L176 c h3 h14 h10 h1 h9 h4 h7 h16 h0 h5 h17 h8 h12 h6).trans (M176 c h3 h14 h10 h1 h9 h4 h7 h16 h0 h5 h17 h8 h12 h6).symm
                          · cases h13 : c.b13
                            · exact (L11 c h8 h0 h12 h3 h4 h17 h16 h6 h10 h5 h1 h7 h13 h9).trans (M11 c h8 h0 h12 h3 h4 h17 h16 h6 h10 h5 h1 h7 h13 h9).symm
                            · exact (L328 c h6 h8 h12 h13 h1 h3 h10 h0 h9 h5 h16 h4 h17 h7).trans (M328 c h6 h8 h12 h13 h1 h3 h10 h0 h9 h5 h16 h4 h17 h7).symm
                    · cases h14 : c.b14
                      · exact (L190 c h0 h3 h6 h5 h14 h10 h16 h17 h7 h12 h1).trans (M190 c h0 h3 h6 h5 h14 h10 h16 h17 h7 h12 h1).symm
                      · cases h4 : c.b4
                        · cases h11 : c.b11
                          · cases h13 : c.b13
                            · exact (L220 c h7 h13 h1 h4 h17 h6 h12 h11 h10 h5 h0 h3 h14 h16).trans (M220 c h7 h13 h1 h4 h17 h6 h12 h11 h10 h5 h0 h3 h14 h16).symm
                            · exact (L179 c h1 h12 h4 h10 h13 h6 h5 h14 h7 h3 h11 h17 h0 h16).trans (M179 c h1 h12 h4 h10 h13 h6 h5 h14 h7 h3 h11 h17 h0 h16).symm
                          · exact (L389 c h12 h0 h5 h11 h16 h14 h4 h10 h6 h1 h3 h7 h17).trans (M389 c h12 h0 h5 h11 h16 h14 h4 h10 h6 h1 h3 h7 h17).symm
                        · exact (L313 c h12 h1 h7 h4 h5 h17 h16 h10 h6 h0 h3 h14).trans (M313 c h12 h1 h7 h4 h5 h17 h16 h10 h6 h0 h3 h14).symm
                · cases h4 : c.b4
                  · exact (L27 c h12 h0 h1 h6 h4 h3 h10 h17 h7).trans (M27 c h12 h0 h1 h6 h4 h3 h10 h17 h7).symm
                  · cases h13 : c.b13
                    · cases h8 : c.b8
                      · exact (L440 c h12 h10 h3 h1 h6 h13 h17 h0 h8 h7 h4).trans (M440 c h12 h10 h3 h1 h6 h13 h17 h0 h8 h7 h4).symm
                      · exact (L352 c h6 h13 h10 h7 h4 h8 h17 h0 h12 h1 h3).trans (M352 c h6 h13 h10 h7 h4 h8 h17 h0 h12 h1 h3).symm
                    · exact (L117 c h12 h0 h17 h4 h1 h7 h3 h10 h6 h13).trans (M117 c h12 h0 h17 h4 h1 h7 h3 h10 h6 h13).symm
            · cases h5 : c.b5
              · cases h15 : c.b15
                · exact (L490 c h6 h0 h12 h17 h15 h1 h7 h5).trans (M490 c h6 h0 h12 h17 h15 h1 h7 h5).symm
                · cases h10 : c.b10
                  · cases h2 : c.b2
                    · cases h8 : c.b8
                      · exact (L383 c h2 h1 h5 h12 h15 h10 h0 h6 h7 h8 h17).trans (M383 c h2 h1 h5 h12 h15 h10 h0 h6 h7 h8 h17).symm
                      · cases h16 : c.b16
                        · exact (L125 c h7 h1 h12 h0 h2 h16 h15 h6 h10 h8 h5 h17).trans (M125 c h7 h1 h12 h0 h2 h16 h15 h6 h10 h8 h5 h17).symm
                        · exact (L93 c h10 h12 h5 h8 h0 h7 h16 h17 h15 h2 h1 h6).trans (M93 c h10 h12 h5 h8 h0 h7 h16 h17 h15 h2 h1 h6).symm
                    · cases h4 : c.b4
                      · cases h14 : c.b14
                        · cases h8 : c.b8
                          · exact (L12 c h8 h7 h12 h1 h10 h0 h6 h2 h14 h15 h5 h4 h17).trans (M12 c h8 h7 h12 h1 h10 h0 h6 h2 h14 h15 h5 h4 h17).symm
                          · exact (L385 c h6 h12 h10 h2 h4 h15 h17 h8 h5 h1 h14 h7 h0).trans (M385 c h6 h12 h10 h2 h4 h15 h17 h8 h5 h1 h14 h7 h0).symm
                        · exact (L213 c h15 h4 h2 h17 h0 h5 h14 h10 h6 h7 h12 h1).trans (M213 c h15 h4 h2 h17 h0 h5 h14 h10 h6 h7 h12 h1).symm
                      · cases h13 : c.b13
                        · cases h14 : c.b14
                          · exact (L350 c h6 h12 h4 h17 h5 h10 h2 h13 h0 h14 h1 h7 h15).trans (M350 c h6 h12 h4 h17 h5 h10 h2 h13 h0 h14 h1 h7 h15).symm
                          · cases h16 : c.b16
                            · exact (L421 c h0 h4 h12 h17 h1 h13 h15 h7 h2 h6 h10 h5 h14 h16).trans (M421 c h0 h4 h12 h17 h1 h13 h15 h7 h2 h6 h10 h5 h14 h16).symm
                            · exact (L28 c h0 h10 h13 h5 h17 h6 h16 h12 h15 h14 h1 h2 h4 h7).trans (M28 c h0 h10 h13 h5 h17 h6 h16 h12 h15 h14 h1 h2 h4 h7).symm
                        · cases h11 : c.b11
                          · exact (L446 c h15 h2 h1 h0 h4 h13 h7 h5 h17 h6 h11 h10 h12).trans (M446 c h15 h2 h1 h0 h4 h13 h7 h5 h17 h6 h11 h10 h12).symm
                          · exact (L325 c h10 h12 h17 h0 h13 h2 h15 h11 h5 h4 h7 h1 h6).trans (M325 c h10 h12 h17 h0 h13 h2 h15 h11 h5 h4 h7 h1 h6).symm
                  · cases h13 : c.b13
                    · cases h16 : c.b16
                      · exact (L477 c h12 h0 h7 h17 h1 h10 h16 h6 h15 h13 h5).trans (M477 c h12 h0 h7 h17 h1 h10 h16 h6 h15 h13 h5).symm
                      · exact (L107 c h17 h13 h16 h15 h0 h6 h10 h12 h5 h1 h7).trans (M107 c h17 h13 h16 h15 h0 h6 h10 h12 h5 h1 h7).symm
                    · cases h4 : c.b4
                      · exact (L365 c h10 h13 h0 h1 h17 h15 h12 h5 h4 h6 h7).trans (M365 c h10 h13 h0 h1 h17 h15 h12 h5 h4 h6 h7).symm
                      · exact (L52 c h0 h15 h17 h12 h5 h6 h10 h4 h7 h1 h13).trans (M52 c h0 h15 h17 h12 h5 h6 h10 h4 h7 h1 h13).symm
              · cases h14 : c.b14
                · cases h3 : c.b3
                  · cases h10 : c.b10
                    · cases h2 : c.b2
                      · exact (L280 c h17 h6 h2 h0 h12 h1 h5 h3 h7 h10 h14).trans (M280 c h17 h6 h2 h0 h12 h1 h5 h3 h7 h10 h14).symm
                      · exact (L23 c h2 h5 h12 h1 h7 h14 h17 h6 h10 h3 h0).trans (M23 c h2 h5 h12 h1 h7 h14 h17 h6 h10 h3 h0).symm
                    · cases h9 : c.b9
                      · exact (L141 c h12 h9 h0 h3 h5 h17 h7 h14 h6 h10 h1).trans (M141 c h12 h9 h0 h3 h5 h17 h7 h14 h6 h10 h1).symm
                      · exact (L262 c h17 h0 h1 h3 h14 h6 h5 h10 h12 h7 h9).trans (M262 c h17 h0 h1 h3 h14 h6 h5 h10 h12 h7 h9).symm
                  · cases h4 : c.b4
                    · exact (L144 c h12 h6 h7 h3 h0 h1 h5 h14 h17 h4).trans (M144 c h12 h6 h7 h3 h0 h1 h5 h14 h17 h4).symm
                    · exact (L236 c h0 h3 h6 h7 h14 h5 h17 h12 h1 h4).trans (M236 c h0 h3 h6 h7 h14 h5 h17 h12 h1 h4).symm
                · cases h13 : c.b13
                  · cases h15 : c.b15
                    · exact (L464 c h7 h6 h13 h1 h17 h5 h12 h0 h14 h15).trans (M464 c h7 h6 h13 h1 h17 h5 h12 h0 h14 h15).symm
                    · exact (L272 c h7 h17 h15 h12 h6 h14 h13 h5 h0 h1).trans (M272 c h7 h17 h15 h12 h6 h14 h13 h5 h0 h1).symm
                  · cases h16 : c.b16
                    · exact (L315 c h6 h16 h0 h13 h12 h14 h1 h5 h7 h17).trans (M315 c h6 h16 h0 h13 h12 h14 h1 h5 h7 h17).symm
                    · cases h2 : c.b2
                      · exact (L119 c h13 h17 h2 h12 h7 h14 h0 h1 h6 h5 h16).trans (M119 c h13 h17 h2 h12 h7 h14 h0 h1 h6 h5 h16).symm
                      · cases h3 : c.b3
                        · cases h11 : c.b11
                          · cases h15 : c.b15
                            · cases h8 : c.b8
                              · exact (L151 c h6 h14 h13 h17 h15 h3 h7 h2 h11 h5 h0 h12 h16 h8 h1).trans (M151 c h6 h14 h13 h17 h15 h3 h7 h2 h11 h5 h0 h12 h16 h8 h1).symm
                              · exact (L112 c h11 h0 h12 h15 h1 h5 h16 h7 h13 h14 h8 h6 h17 h3 h2).trans (M112 c h11 h0 h12 h15 h1 h5 h16 h7 h13 h14 h8 h6 h17 h3 h2).symm
                            · cases h4 : c.b4
                              · exact (L447 c h12 h17 h1 h15 h7 h3 h16 h14 h4 h5 h13 h6 h2 h0 h11).trans (M447 c h12 h17 h1 h15 h7 h3 h16 h14 h4 h5 h13 h6 h2 h0 h11).symm
                              · cases h8 : c.b8
                                · exact (L126 c h16 h3 h2 h15 h12 h13 h1 h4 h8 h6 h0 h14 h17 h11 h5 h7).trans (M126 c h16 h3 h2 h15 h12 h13 h1 h4 h8 h6 h0 h14 h17 h11 h5 h7).symm
                                · cases h10 : c.b10
                                  · exact (L230 c h10 h15 h2 h3 h12 h11 h8 h6 h0 h7 h13 h4 h14 h16 h5 h17 h1).trans (M230 c h10 h15 h2 h3 h12 h11 h8 h6 h0 h7 h13 h4 h14 h16 h5 h17 h1).symm
                                  · exact (L387 c h7 h13 h1 h10 h6 h17 h16 h2 h3 h15 h5 h12 h4 h8 h14 h0 h11).trans (M387 c h7 h13 h1 h10 h6 h17 h16 h2 h3 h15 h5 h12 h4 h8 h14 h0 h11).symm
                          · cases h10 : c.b10
                            · cases h8 : c.b8
                              · cases h4 : c.b4
                                · cases h9 : c.b9
                                  · exact (L149 c h5 h2 h13 h12 h3 h0 h4 h11 h16 h10 h14 h1 h17 h8 h6 h9 h7).trans (M149 c h5 h2 h13 h12 h3 h0 h4 h11 h16 h10 h14 h1 h17 h8 h6 h9 h7).symm
                                  · exact (L278 c h14 h2 h3 h8 h17 h1 h7 h4 h13 h12 h9 h0 h16 h10 h6 h11 h5).trans (M278 c h14 h2 h3 h8 h17 h1 h7 h4 h13 h12 h9 h0 h16 h10 h6 h11 h5).symm
                                · cases h15 : c.b15
                                  · cases h9 : c.b9
                                    · exact (L291 c h6 h14 h13 h9 h1 h15 h3 h8 h10 h12 h17 h0 h16 h7 h11 h4 h5 h2).trans (M291 c h6 h14 h13 h9 h1 h15 h3 h8 h10 h12 h17 h0 h16 h7 h11 h4 h5 h2).symm
                                    · exact (L439 c h10 h7 h1 h5 h11 h14 h15 h0 h13 h16 h9 h3 h17 h8 h12 h6 h4 h2).trans (M439 c h10 h7 h1 h5 h11 h14 h15 h0 h13 h16 h9 h3 h17 h8 h12 h6 h4 h2).symm
                                  · exact (L155 c h15 h14 h16 h0 h2 h11 h6 h7 h13 h1 h10 h8 h5 h4 h3 h12 h17).trans (M155 c h15 h14 h16 h0 h2 h11 h6 h7 h13 h1 h10 h8 h5 h4 h3 h12 h17).symm
                              · exact (L80 c h5 h11 h13 h10 h6 h8 h7 h1 h16 h3 h14 h17 h2 h12 h0).trans (M80 c h5 h11 h13 h10 h6 h8 h7 h1 h16 h3 h14 h17 h2 h12 h0).symm
                            · cases h4 : c.b4
                              · exact (L507 c h11 h12 h4 h1 h7 h2 h14 h3 h17 h10 h16 h6 h5 h13 h0).trans (M507 c h11 h12 h4 h1 h7 h2 h14 h3 h17 h10 h16 h6 h5 h13 h0).symm
                              · exact (L259 c h11 h2 h7 h1 h0 h6 h3 h14 h12 h17 h10 h16 h5 h4 h13).trans (M259 c h11 h2 h7 h1 h0 h6 h3 h14 h12 h17 h10 h16 h5 h4 h13).symm
                        · exact (L288 c h0 h12 h7 h17 h1 h6 h3 h14 h13 h16 h5 h2).trans (M288 c h0 h12 h7 h17 h1 h6 h3 h14 h13 h16 h5 h2).symm
      · cases h10 : c.b10
        · cases h12 : c.b12
          · cases h17 : c.b17
            · cases h15 : c.b15
              · cases h14 : c.b14
                · cases h3 : c.b3
                  · exact (L482 c h10 h14 h1 h0 h17 h3 h12 h6 h15).trans (M482 c h10 h14 h1 h0 h17 h3 h12 h6 h15).symm
                  · exact (L133 c h17 h3 h6 h10 h14 h12 h15 h0 h1).trans (M133 c h17 h3 h6 h10 h14 h12 h15 h0 h1).symm
                · cases h7 : c.b7
                  · exact (L406 c h17 h10 h15 h0 h7 h14 h6 h1 h12).trans (M406 c h17 h10 h15 h0 h7 h14 h6 h1 h12).symm
                  · exact (L8 c h17 h10 h6 h12 h0 h7 h14 h15 h1).trans (M8 c h17 h10 h6 h12 h0 h7 h14 h15 h1).symm
              · cases h2 : c.b2
                · cases h13 : c.b13
                  · exact (L38 c h0 h1 h17 h15 h6 h2 h12 h10 h13).trans (M38 c h0 h1 h17 h15 h6 h2 h12 h10 h13).symm
                  · cases h4 : c.b4
                    · exact (L330 c h4 h13 h1 h12 h15 h0 h17 h2 h6 h10).trans (M330 c h4 h13 h1 h12 h15 h0 h17 h2 h6 h10).symm
                    · cases h8 : c.b8
                      · cases h3 : c.b3
                        · exact (L215 c h2 h15 h0 h8 h12 h10 h1 h17 h13 h4 h3 h6).trans (M215 c h2 h15 h0 h8 h12 h10 h1 h17 h13 h4 h3 h6).symm
                        · exact (L400 c h17 h12 h4 h2 h13 h3 h0 h6 h1 h8 h10 h15).trans (M400 c h17 h12 h4 h2 h13 h3 h0 h6 h1 h8 h10 h15).symm
                      · cases h11 : c.b11
                        · exact (L432 c h12 h2 h10 h0 h1 h17 h11 h8 h6 h13 h15 h4).trans (M432 c h12 h2 h10 h0 h1 h17 h11 h8 h6 h13 h15 h4).symm
                        · exact (L412 c h10 h12 h0 h15 h8 h4 h2 h17 h1 h11 h6 h13).trans (M412 c h10 h12 h0 h15 h8 h4 h2 h17 h1 h11 h6 h13).symm
                · cases h13 : c.b13
                  · cases h3 : c.b3
                    · cases h4 : c.b4
                      · exact (L83 c h1 h12 h13 h6 h2 h3 h17 h10 h15 h0 h4).trans (M83 c h1 h12 h13 h6 h2 h3 h17 h10 h15 h0 h4).symm
                      · exact (L118 c h0 h1 h10 h13 h12 h17 h4 h3 h2 h6 h15).trans (M118 c h0 h1 h10 h13 h12 h17 h4 h3 h2 h6 h15).symm
                    · cases h14 : c.b14
                      · exact (L98 c h13 h14 h17 h0 h3 h6 h2 h1 h12 h10 h15).trans (M98 c h13 h14 h17 h0 h3 h6 h2 h1 h12 h10 h15).symm
                      · exact (L381 c h3 h6 h15 h10 h12 h17 h2 h0 h1 h13 h14).trans (M381 c h3 h6 h15 h10 h12 h17 h2 h0 h1 h13 h14).symm
                  · cases h4 : c.b4
                    · cases h11 : c.b11
                      · exact (L467 c h11 h13 h17 h10 h15 h2 h1 h0 h12 h6 h4).trans (M467 c h11 h13 h17 h10 h15 h2 h1 h0 h12 h6 h4).symm
                      · exact (L494 c h11 h0 h10 h4 h13 h12 h15 h17 h2 h6 h1).trans (M494 c h11 h0 h10 h4 h13 h12 h15 h17 h2 h6 h1).symm
                    · cases h8 : c.b8
                      · exact (L354 c h6 h1 h17 h0 h4 h15 h12 h2 h8 h13 h10).trans (M354 c h6 h1 h17 h0 h4 h15 h12 h2 h8 h13 h10).symm
                      · cases h9 : c.b9
                        · exact (L297 c h6 h2 h1 h10 h4 h12 h0 h8 h9 h15 h17 h13).trans (M297 c h6 h2 h1 h10 h4 h12 h0 h8 h9 h15 h17 h13).symm
                        · cases h7 : c.b7
                          · cases h5 : c.b5
                            · exact (L486 c h1 h6 h5 h17 h8 h0 h2 h4 h13 h10 h7 h15 h9 h12).trans (M486 c h1 h6 h5 h17 h8 h0 h2 h4 h13 h10 h7 h15 h9 h12).symm
                            · cases h16 : c.b16
                              · exact (L165 c h7 h17 h8 h1 h15 h0 h6 h4 h10 h13 h2 h16 h12 h9 h5).trans (M165 c h7 h17 h8 h1 h15 h0 h6 h4 h10 h13 h2 h16 h12 h9 h5).symm
                              · exact (L101 c h0 h12 h2 h1 h10 h4 h8 h6 h16 h15 h17 h5 h13 h7 h9).trans (M101 c h0 h12 h2 h1 h10 h4 h8 h6 h16 h15 h17 h5 h13 h7 h9).symm
                          · exact (L483 c h10 h7 h2 h17 h0 h8 h12 h6 h15 h13 h1 h9 h4).trans (M483 c h10 h7 h2 h17 h0 h8 h12 h6 h15 h13 h1 h9 h4).symm
            · cases h4 : c.b4
              · cases h9 : c.b9
                · exact (L290 c h10 h12 h9 h4 h6 h0 h1 h17).trans (M290 c h10 h12 h9 h4 h6 h0 h1 h17).symm
                · cases h16 : c.b16
                  · cases h15 : c.b15
                    · cases h13 : c.b13
                      · exact (L210 c h1 h0 h17 h6 h12 h16 h4 h15 h10 h9 h13).trans (M210 c h1 h0 h17 h6 h12 h16 h4 h15 h10 h9 h13).symm
                      · exact (L361 c h1 h4 h10 h9 h15 h13 h0 h6 h16 h12 h17).trans (M361 c h1 h4 h10 h9 h15 h13 h0 h6 h16 h12 h17).symm
                    · exact (L270 c h12 h17 h9 h6 h10 h1 h16 h4 h15 h0).trans (M270 c h12 h17 h9 h6 h10 h1 h16 h4 h15 h0).symm
                  · cases h14 : c.b14
                    · cases h15 : c.b15
                      · exact (L135 c h4 h10 h15 h17 h9 h0 h6 h14 h16 h12 h1).trans (M135 c h4 h10 h15 h17 h9 h0 h6 h14 h16 h12 h1).symm
                      · cases h3 : c.b3
                        · exact (L103 c h3 h15 h4 h16 h12 h0 h9 h10 h14 h17 h6 h1).trans (M103 c h3 h15 h4 h16 h12 h0 h9 h10 h14 h17 h6 h1).symm
                        · exact (L285 c h15 h1 h6 h4 h10 h16 h3 h9 h0 h12 h17 h14).trans (M285 c h15 h1 h6 h4 h10 h16 h3 h9 h0 h12 h17 h14).symm
                    · cases h5 : c.b5
                      · cases h8 : c.b8
                        · cases h15 : c.b15
                          · cases h11 : c.b11
                            · cases h13 : c.b13
                              · exact (L234 c h9 h5 h0 h10 h11 h8 h15 h1 h17 h13 h14 h4 h16 h6 h12).trans (M234 c h9 h5 h0 h10 h11 h8 h15 h1 h17 h13 h14 h4 h16 h6 h12).symm
                              · exact (L242 c h13 h6 h5 h0 h8 h11 h4 h16 h17 h14 h10 h1 h9 h15 h12).trans (M242 c h13 h6 h5 h0 h8 h11 h4 h16 h17 h14 h10 h1 h9 h15 h12).symm
                            · exact (L153 c h16 h17 h6 h10 h8 h9 h12 h4 h14 h1 h0 h15 h11 h5).trans (M153 c h16 h17 h6 h10 h8 h9 h12 h4 h14 h1 h0 h15 h11 h5).symm
                          · cases h7 : c.b7
                            · exact (L30 c h4 h0 h10 h9 h8 h5 h7 h12 h1 h6 h17 h14 h16 h15).trans (M30 c h4 h0 h10 h9 h8 h5 h7 h12 h1 h6 h17 h14 h16 h15).symm
                            · exact (L70 c h12 h15 h9 h8 h7 h17 h4 h1 h5 h6 h16 h10 h0 h14).trans (M70 c h12 h15 h9 h8 h7 h17 h4 h1 h5 h6 h16 h10 h0 h14).symm
                        · exact (L169 c h9 h0 h6 h14 h8 h17 h1 h5 h4 h16 h10 h12).trans (M169 c h9 h0 h6 h14 h8 h17 h1 h5 h4 h16 h10 h12).symm
                      · cases h11 : c.b11
                        · exact (L79 c h6 h17 h5 h14 h0 h10 h4 h11 h16 h1 h9 h12).trans (M79 c h6 h17 h5 h14 h0 h10 h4 h11 h16 h1 h9 h12).symm
                        · exact (L62 c h1 h10 h5 h6 h16 h17 h12 h9 h14 h4 h11 h0).trans (M62 c h1 h10 h5 h6 h16 h17 h12 h9 h14 h4 h11 h0).symm
              · cases h2 : c.b2
                · cases h16 : c.b16
                  · cases h9 : c.b9
                    · exact (L59 c h9 h17 h1 h0 h10 h6 h16 h2 h4 h12).trans (M59 c h9 h17 h1 h0 h10 h6 h16 h2 h4 h12).symm
                    · cases h15 : c.b15
                      · exact (L376 c h10 h16 h0 h2 h4 h1 h15 h12 h17 h9 h6).trans (M376 c h10 h16 h0 h2 h4 h1 h15 h12 h17 h9 h6).symm
                      · exact (L282 c h16 h12 h10 h9 h2 h6 h17 h1 h0 h4 h15).trans (M282 c h16 h12 h10 h9 h2 h6 h17 h1 h0 h4 h15).symm
                  · cases h14 : c.b14
                    · cases h7 : c.b7
                      · exact (L456 c h6 h7 h1 h4 h12 h2 h10 h14 h17 h0 h16).trans (M456 c h6 h7 h1 h4 h12 h2 h10 h14 h17 h0 h16).symm
                      · exact (L310 c h12 h7 h6 h2 h14 h10 h16 h4 h17 h1 h0).trans (M310 c h12 h7 h6 h2 h14 h10 h16 h4 h17 h1 h0).symm
                    · cases h11 : c.b11
                      · cases h3 : c.b3
                        · exact (L65 c h17 h6 h2 h11 h1 h12 h14 h16 h10 h0 h4 h3).trans (M65 c h17 h6 h2 h11 h1 h12 h14 h16 h10 h0 h4 h3).symm
                        · exact (L246 c h11 h10 h0 h1 h16 h4 h6 h12 h3 h17 h2 h14).trans (M246 c h11 h10 h0 h1 h16 h4 h6 h12 h3 h17 h2 h14).symm
                      · exact (L465 c h4 h12 h11 h14 h16 h17 h1 h2 h0 h10 h6).trans (M465 c h4 h12 h11 h14 h16 h17 h1 h2 h0 h10 h6).symm
                · exact (L498 c h0 h2 h6 h1 h4 h17 h10 h12).trans (M498 c h0 h2 h6 h1 h4 h17 h10 h12).symm
          · cases h9 : c.b9
            · cases h11 : c.b11
              · cases h14 : c.b14
                · cases h15 : c.b15
                  · cases h13 : c.b13
                    · exact (L299 c h0 h1 h14 h12 h9 h6 h10 h11 h15 h13).trans (M299 c h0 h1 h14 h12 h9 h6 h10 h11 h15 h13).symm
                    · exact (L231 c h13 h12 h11 h0 h9 h6 h15 h10 h1 h14).trans (M231 c h13 h12 h11 h0 h9 h6 h15 h10 h1 h14).symm
                  · cases h8 : c.b8
                    · cases h3 : c.b3
                      · cases h13 : c.b13
                        · exact (L106 c h1 h13 h12 h6 h10 h0 h11 h9 h8 h3 h14 h15).trans (M106 c h1 h13 h12 h6 h10 h0 h11 h9 h8 h3 h14 h15).symm
                        · cases h7 : c.b7
                          · exact (L481 c h1 h11 h12 h6 h7 h0 h13 h15 h10 h9 h14 h3 h8).trans (M481 c h1 h11 h12 h6 h7 h0 h13 h15 h10 h9 h14 h3 h8).symm
                          · exact (L372 c h12 h6 h15 h11 h14 h10 h0 h3 h1 h8 h7 h13 h9).trans (M372 c h12 h6 h15 h11 h14 h10 h0 h3 h1 h8 h7 h13 h9).symm
                      · cases h13 : c.b13
                        · exact (L0 c h1 h11 h13 h9 h3 h8 h12 h10 h15 h0 h14 h6).trans (M0 c h1 h11 h13 h9 h3 h8 h12 h10 h15 h0 h14 h6).symm
                        · exact (L358 c h1 h0 h10 h11 h6 h8 h12 h15 h13 h9 h14 h3).trans (M358 c h1 h0 h10 h11 h6 h8 h12 h15 h13 h9 h14 h3).symm
                    · cases h16 : c.b16
                      · exact (L47 c h11 h14 h0 h10 h8 h9 h1 h15 h6 h16 h12).trans (M47 c h11 h14 h0 h10 h8 h9 h1 h15 h6 h16 h12).symm
                      · exact (L349 c h16 h12 h8 h6 h10 h0 h15 h1 h14 h9 h11).trans (M349 c h16 h12 h8 h6 h10 h0 h15 h1 h14 h9 h11).symm
                · exact (L75 c h12 h6 h0 h10 h9 h1 h14 h11).trans (M75 c h12 h6 h0 h10 h9 h1 h14 h11).symm
              · cases h7 : c.b7
                · cases h13 : c.b13
                  · exact (L136 c h12 h0 h7 h1 h9 h11 h6 h13 h10).trans (M136 c h12 h0 h7 h1 h9 h11 h6 h13 h10).symm
                  · cases h2 : c.b2
                    · exact (L104 c h9 h13 h2 h10 h12 h1 h11 h0 h6 h7).trans (M104 c h9 h13 h2 h10 h12 h1 h11 h0 h6 h7).symm
                    · exact (L167 c h6 h11 h9 h13 h7 h12 h1 h0 h2 h10).trans (M167 c h6 h11 h9 h13 h7 h12 h1 h0 h2 h10).symm
                · cases h2 : c.b2
                  · exact (L473 c h6 h10 h11 h2 h9 h7 h0 h12 h1).trans (M473 c h6 h10 h11 h2 h9 h7 h0 h12 h1).symm
                  · exact (L335 c h1 h2 h6 h9 h10 h11 h0 h7 h12).trans (M335 c h1 h2 h6 h9 h10 h11 h0 h7 h12).symm
            · cases h15 : c.b15
              · cases h8 : c.b8
                · cases h11 : c.b11
                  · exact (L452 c h10 h15 h11 h9 h12 h6 h0 h8 h1).trans (M452 c h10 h15 h11 h9 h12 h6 h0 h8 h1).symm
                  · cases h16 : c.b16
                    · cases h2 : c.b2
                      · cases h14 : c.b14
                        · cases h4 : c.b4
                          · exact (L363 c h10 h1 h16 h2 h0 h14 h12 h8 h9 h15 h4 h11 h6).trans (M363 c h10 h1 h16 h2 h0 h14 h12 h8 h9 h15 h4 h11 h6).symm
                          · cases h7 : c.b7
                            · exact (L203 c h12 h6 h9 h1 h15 h2 h14 h0 h11 h8 h4 h16 h7 h10).trans (M203 c h12 h6 h9 h1 h15 h2 h14 h0 h11 h8 h4 h16 h7 h10).symm
                            · exact (L41 c h15 h14 h6 h16 h11 h0 h4 h10 h9 h1 h2 h12 h8 h7).trans (M41 c h15 h14 h6 h16 h11 h0 h4 h10 h9 h1 h2 h12 h8 h7).symm
                        · exact (L308 c h10 h12 h6 h16 h2 h0 h1 h9 h14 h8 h15 h11).trans (M308 c h10 h12 h6 h16 h2 h0 h1 h9 h14 h8 h15 h11).symm
                      · cases h13 : c.b13
                        · exact (L491 c h16 h11 h0 h2 h15 h12 h6 h1 h9 h13 h8 h10).trans (M491 c h16 h11 h0 h2 h15 h12 h6 h1 h9 h13 h8 h10).symm
                        · exact (L53 c h12 h11 h1 h9 h13 h0 h8 h10 h2 h15 h16 h6).trans (M53 c h12 h11 h1 h9 h13 h0 h8 h10 h2 h15 h16 h6).symm
                    · exact (L249 c h11 h16 h1 h0 h12 h9 h10 h6 h8 h15).trans (M249 c h11 h16 h1 h0 h12 h9 h10 h6 h8 h15).symm
                · cases h11 : c.b11
                  · cases h16 : c.b16
                    · cases h5 : c.b5
                      · cases h2 : c.b2
                        · exact (L197 c h11 h6 h15 h0 h1 h12 h16 h8 h10 h5 h2 h9).trans (M197 c h11 h6 h15 h0 h1 h12 h16 h8 h10 h5 h2 h9).symm
                        · exact (L208 c h12 h8 h11 h2 h0 h5 h1 h10 h9 h15 h16 h6).trans (M208 c h12 h8 h11 h2 h0 h5 h1 h10 h9 h15 h16 h6).symm
                      · cases h4 : c.b4
                        · exact (L324 c h12 h11 h5 h9 h15 h10 h1 h8 h16 h6 h4 h0).trans (M324 c h12 h11 h5 h9 h15 h10 h1 h8 h16 h6 h4 h0).symm
                        · exact (L384 c h12 h5 h9 h6 h4 h1 h10 h0 h15 h8 h16 h11).trans (M384 c h12 h5 h9 h6 h4 h1 h10 h0 h15 h8 h16 h11).symm
                    · exact (L334 c h1 h6 h16 h8 h9 h15 h10 h12 h11 h0).trans (M334 c h1 h6 h16 h8 h9 h15 h10 h12 h11 h0).symm
                  · cases h3 : c.b3
                    · cases h7 : c.b7
                      · cases h4 : c.b4
                        · cases h13 : c.b13
                          · exact (L305 c h12 h13 h9 h4 h3 h6 h10 h1 h0 h8 h11 h7 h15).trans (M305 c h12 h13 h9 h4 h3 h6 h10 h1 h0 h8 h11 h7 h15).symm
                          · exact (L502 c h4 h10 h12 h7 h15 h11 h13 h1 h9 h3 h0 h6 h8).trans (M502 c h4 h10 h12 h7 h15 h11 h13 h1 h9 h3 h0 h6 h8).symm
                        · exact (L120 c h15 h9 h1 h8 h12 h7 h10 h6 h0 h11 h4 h3).trans (M120 c h15 h9 h1 h8 h12 h7 h10 h6 h0 h11 h4 h3).symm
                      · cases h17 : c.b17
                        · exact (L178 c h8 h0 h9 h6 h3 h15 h7 h11 h17 h12 h10 h1).trans (M178 c h8 h0 h9 h6 h3 h15 h7 h11 h17 h12 h10 h1).symm
                        · exact (L508 c h12 h8 h10 h11 h7 h3 h9 h1 h0 h15 h17 h6).trans (M508 c h12 h8 h10 h11 h7 h3 h9 h1 h0 h15 h17 h6).symm
                    · cases h7 : c.b7
                      · cases h4 : c.b4
                        · exact (L329 c h15 h12 h10 h7 h8 h9 h11 h1 h4 h6 h3 h0).trans (M329 c h15 h12 h10 h7 h8 h9 h11 h1 h4 h6 h3 h0).symm
                        · exact (L289 c h10 h9 h11 h15 h1 h12 h3 h6 h7 h8 h4 h0).trans (M289 c h10 h9 h11 h15 h1 h12 h3 h6 h7 h8 h4 h0).symm
                      · exact (L307 c h9 h6 h7 h11 h12 h1 h0 h15 h10 h3 h8).trans (M307 c h9 h6 h7 h11 h12 h1 h0 h15 h10 h3 h8).symm
              · cases h4 : c.b4
                · exact (L318 c h4 h12 h1 h6 h15 h9 h0 h10).trans (M318 c h4 h12 h1 h6 h15 h9 h0 h10).symm
                · cases h14 : c.b14
                  · cases h5 : c.b5
                    · cases h8 : c.b8
                      · cases h3 : c.b3
                        · cases h16 : c.b16
                          · exact (L31 c h1 h12 h0 h16 h14 h8 h15 h10 h9 h3 h4 h6 h5).trans (M31 c h1 h12 h0 h16 h14 h8 h15 h10 h9 h3 h4 h6 h5).symm
                          · cases h7 : c.b7
                            · cases h11 : c.b11
                              · exact (L492 c h12 h10 h9 h14 h0 h15 h8 h11 h5 h7 h3 h16 h4 h1 h6).trans (M492 c h12 h10 h9 h14 h0 h15 h8 h11 h5 h7 h3 h16 h4 h1 h6).symm
                              · cases h13 : c.b13
                                · exact (L58 c h1 h10 h7 h15 h16 h8 h13 h4 h14 h0 h6 h3 h12 h5 h9 h11).trans (M58 c h1 h10 h7 h15 h16 h8 h13 h4 h14 h0 h6 h3 h12 h5 h9 h11).symm
                                · cases h17 : c.b17
                                  · exact (L128 c h1 h11 h10 h0 h8 h3 h6 h4 h5 h16 h17 h14 h15 h12 h7 h9 h13).trans (M128 c h1 h11 h10 h0 h8 h3 h6 h4 h5 h16 h17 h14 h15 h12 h7 h9 h13).symm
                                  · exact (L257 c h8 h17 h11 h10 h3 h0 h5 h9 h16 h7 h14 h6 h1 h12 h4 h13 h15).trans (M257 c h8 h17 h11 h10 h3 h0 h5 h9 h16 h7 h14 h6 h1 h12 h4 h13 h15).symm
                            · cases h2 : c.b2
                              · cases h11 : c.b11
                                · cases h13 : c.b13
                                  · cases h17 : c.b17
                                    · exact (L193 c h12 h9 h6 h10 h0 h3 h16 h15 h1 h11 h13 h5 h8 h17 h4 h14 h2 h7).trans (M193 c h12 h9 h6 h10 h0 h3 h16 h15 h1 h11 h13 h5 h8 h17 h4 h14 h2 h7).symm
                                    · exact (L503 c h16 h17 h13 h0 h5 h12 h3 h14 h1 h2 h4 h9 h11 h7 h8 h6 h10 h15).trans (M503 c h16 h17 h13 h0 h5 h12 h3 h14 h1 h2 h4 h9 h11 h7 h8 h6 h10 h15).symm
                                  · exact (L273 c h0 h11 h8 h6 h9 h16 h2 h10 h15 h14 h4 h12 h13 h7 h5 h3 h1).trans (M273 c h0 h11 h8 h6 h9 h16 h2 h10 h15 h14 h4 h12 h13 h7 h5 h3 h1).symm
                                · cases h13 : c.b13
                                  · cases h17 : c.b17
                                    · exact (L407 c h16 h6 h2 h3 h5 h7 h14 h13 h4 h17 h1 h15 h12 h8 h9 h10 h0 h11).trans (M407 c h16 h6 h2 h3 h5 h7 h14 h13 h4 h17 h1 h15 h12 h8 h9 h10 h0 h11).symm
                                    · exact (L497 c h12 h9 h15 h11 h17 h6 h10 h8 h2 h1 h7 h0 h5 h14 h3 h13 h4 h16).trans (M497 c h12 h9 h15 h11 h17 h6 h10 h8 h2 h1 h7 h0 h5 h14 h3 h13 h4 h16).symm
                                  · exact (L216 c h9 h14 h2 h0 h4 h16 h11 h12 h7 h1 h15 h10 h8 h5 h6 h13 h3).trans (M216 c h9 h14 h2 h0 h4 h16 h11 h12 h7 h1 h15 h10 h8 h5 h6 h13 h3).symm
                              · cases h17 : c.b17
                                · cases h13 : c.b13
                                  · exact (L4 c h9 h5 h4 h1 h14 h10 h13 h0 h7 h2 h17 h16 h8 h6 h3 h12 h15).trans (M4 c h9 h5 h4 h1 h14 h10 h13 h0 h7 h2 h17 h16 h8 h6 h3 h12 h15).symm
                                  · cases h11 : c.b11
                                    · exact (L147 c h1 h17 h5 h0 h14 h11 h16 h8 h4 h2 h9 h12 h7 h3 h15 h13 h10 h6).trans (M147 c h1 h17 h5 h0 h14 h11 h16 h8 h4 h2 h9 h12 h7 h3 h15 h13 h10 h6).symm
                                    · exact (L322 c h11 h0 h5 h3 h15 h13 h14 h7 h4 h10 h6 h17 h12 h2 h9 h16 h8 h1).trans (M322 c h11 h0 h5 h3 h15 h13 h14 h7 h4 h10 h6 h17 h12 h2 h9 h16 h8 h1).symm
                                · cases h11 : c.b11
                                  · exact (L82 c h17 h16 h8 h3 h11 h1 h10 h2 h15 h0 h12 h7 h6 h14 h5 h4 h9).trans (M82 c h17 h16 h8 h3 h11 h1 h10 h2 h15 h0 h12 h7 h6 h14 h5 h4 h9).symm
                                  · exact (L194 c h16 h0 h14 h11 h7 h5 h12 h2 h8 h1 h6 h4 h17 h15 h3 h10 h9).trans (M194 c h16 h0 h14 h11 h7 h5 h12 h2 h8 h1 h6 h4 h17 h15 h3 h10 h9).symm
                        · cases h7 : c.b7
                          · exact (L233 c h10 h3 h0 h14 h6 h9 h5 h7 h15 h1 h12 h4 h8).trans (M233 c h10 h3 h0 h14 h6 h9 h5 h7 h15 h1 h12 h4 h8).symm
                          · cases h16 : c.b16
                            · exact (L256 c h15 h14 h0 h10 h9 h8 h4 h5 h16 h7 h1 h12 h6 h3).trans (M256 c h15 h14 h0 h10 h9 h8 h4 h5 h16 h7 h1 h12 h6 h3).symm
                            · cases h11 : c.b11
                              · exact (L33 c h14 h12 h1 h3 h15 h11 h6 h7 h16 h4 h8 h9 h10 h5 h0).trans (M33 c h14 h12 h1 h3 h15 h11 h6 h7 h16 h4 h8 h9 h10 h5 h0).symm
                              · exact (L81 c h3 h6 h11 h10 h5 h12 h15 h1 h9 h16 h7 h14 h0 h4 h8).trans (M81 c h3 h6 h11 h10 h5 h12 h15 h1 h9 h16 h7 h14 h0 h4 h8).symm
                      · cases h7 : c.b7
                        · exact (L152 c h6 h1 h7 h8 h5 h15 h4 h10 h12 h14 h9 h0).trans (M152 c h6 h1 h7 h8 h5 h15 h4 h10 h12 h14 h9 h0).symm
                        · exact (L487 c h7 h1 h4 h14 h10 h8 h9 h15 h0 h12 h5 h6).trans (M487 c h7 h1 h4 h14 h10 h8 h9 h15 h0 h12 h5 h6).symm
                    · cases h8 : c.b8
                      · exact (L488 c h14 h10 h9 h8 h6 h15 h12 h5 h0 h1 h4).trans (M488 c h14 h10 h9 h8 h6 h15 h12 h5 h0 h1 h4).symm
                      · exact (L340 c h12 h5 h14 h1 h10 h0 h4 h6 h15 h9 h8).trans (M340 c h12 h5 h14 h1 h10 h0 h4 h6 h15 h9 h8).symm
                  · cases h2 : c.b2
                    · cases h5 : c.b5
                      · cases h3 : c.b3
                        · cases h7 : c.b7
                          · exact (L353 c h14 h4 h7 h0 h1 h5 h9 h10 h3 h15 h6 h2 h12).trans (M353 c h14 h4 h7 h0 h1 h5 h9 h10 h3 h15 h6 h2 h12).symm
                          · exact (L414 c h6 h7 h14 h15 h3 h2 h10 h1 h5 h9 h12 h0 h4).trans (M414 c h6 h7 h14 h15 h3 h2 h10 h1 h5 h9 h12 h0 h4).symm
                        · exact (L196 c h15 h4 h0 h12 h5 h2 h6 h1 h10 h3 h9 h14).trans (M196 c h15 h4 h0 h12 h5 h2 h6 h1 h10 h3 h9 h14).symm
                      · cases h16 : c.b16
                        · exact (L276 c h1 h16 h10 h4 h2 h0 h6 h5 h9 h12 h14 h15).trans (M276 c h1 h16 h10 h4 h2 h0 h6 h5 h9 h12 h14 h15).symm
                        · cases h11 : c.b11
                          · exact (L312 c h0 h11 h16 h2 h6 h12 h5 h15 h14 h10 h4 h1 h9).trans (M312 c h0 h11 h16 h2 h6 h12 h5 h15 h14 h10 h4 h1 h9).symm
                          · exact (L504 c h11 h9 h0 h12 h16 h1 h5 h4 h2 h14 h15 h6 h10).trans (M504 c h11 h9 h0 h12 h16 h1 h5 h4 h2 h14 h15 h6 h10).symm
                    · cases h3 : c.b3
                      · cases h5 : c.b5
                        · cases h17 : c.b17
                          · exact (L164 c h10 h12 h17 h5 h6 h0 h2 h1 h4 h3 h14 h9 h15).trans (M164 c h10 h12 h17 h5 h6 h0 h2 h1 h4 h3 h14 h9 h15).symm
                          · cases h16 : c.b16
                            · exact (L403 c h5 h1 h2 h17 h4 h12 h3 h16 h10 h15 h9 h14 h6 h0).trans (M403 c h5 h1 h2 h17 h4 h12 h3 h16 h10 h15 h9 h14 h6 h0).symm
                            · exact (L316 c h14 h2 h17 h12 h16 h4 h6 h9 h5 h15 h3 h1 h10 h0).trans (M316 c h14 h2 h17 h12 h16 h4 h6 h9 h5 h15 h3 h1 h10 h0).symm
                        · cases h17 : c.b17
                          · cases h13 : c.b13
                            · exact (L264 c h9 h13 h0 h4 h15 h1 h12 h6 h14 h3 h5 h2 h10 h17).trans (M264 c h9 h13 h0 h4 h15 h1 h12 h6 h14 h3 h5 h2 h10 h17).symm
                            · exact (L226 c h17 h12 h4 h5 h2 h3 h15 h14 h0 h9 h6 h13 h1 h10).trans (M226 c h17 h12 h4 h5 h2 h3 h15 h14 h0 h9 h6 h13 h1 h10).symm
                          · cases h11 : c.b11
                            · exact (L277 c h14 h5 h15 h10 h17 h6 h12 h11 h0 h9 h4 h1 h3 h2).trans (M277 c h14 h5 h15 h10 h17 h6 h12 h11 h0 h9 h4 h1 h3 h2).symm
                            · exact (L209 c h5 h4 h15 h10 h14 h9 h11 h0 h3 h12 h1 h17 h6 h2).trans (M209 c h5 h4 h15 h10 h14 h9 h11 h0 h3 h12 h1 h17 h6 h2).symm
                      · exact (L470 c h12 h3 h10 h9 h0 h2 h4 h6 h15 h1 h14).trans (M470 c h12 h3 h10 h9 h0 h2 h4 h6 h15 h1 h14).symm
        · cases h4 : c.b4
          · cases h16 : c.b16
            · cases h8 : c.b8
              · exact (L336 c h6 h10 h8 h4 h16 h0 h1).trans (M336 c h6 h10 h8 h4 h16 h0 h1).symm
              · exact (L195 c h6 h0 h8 h1 h16 h10 h4).trans (M195 c h6 h0 h8 h1 h16 h10 h4).symm
            · cases h13 : c.b13
              · exact (L163 c h1 h16 h13 h10 h6 h0 h4).trans (M163 c h1 h16 h13 h10 h6 h0 h4).symm
              · cases h7 : c.b7
                · exact (L180 c h10 h7 h6 h0 h16 h13 h1 h4).trans (M180 c h10 h7 h6 h0 h16 h13 h1 h4).symm
                · cases h3 : c.b3
                  · exact (L418 c h7 h0 h1 h10 h16 h6 h3 h4 h13).trans (M418 c h7 h0 h1 h10 h16 h6 h3 h4 h13).symm
                  · exact (L170 c h6 h10 h4 h7 h0 h16 h1 h13 h3).trans (M170 c h6 h10 h4 h7 h0 h16 h1 h13 h3).symm
          · cases h7 : c.b7
            · cases h16 : c.b16
              · cases h2 : c.b2
                · cases h13 : c.b13
                  · exact (L129 c h0 h7 h1 h6 h4 h16 h13 h10 h2).trans (M129 c h0 h7 h1 h6 h4 h16 h13 h10 h2).symm
                  · exact (L237 c h0 h1 h6 h7 h10 h13 h16 h2 h4).trans (M237 c h0 h1 h6 h7 h10 h13 h16 h2 h4).symm
                · exact (L254 c h1 h10 h6 h4 h16 h0 h7 h2).trans (M254 c h1 h10 h6 h4 h16 h0 h7 h2).symm
              · exact (L71 c h1 h10 h6 h7 h0 h4 h16).trans (M71 c h1 h10 h6 h7 h0 h4 h16).symm
            · cases h3 : c.b3
              · exact (L89 c h4 h3 h10 h1 h0 h7 h6).trans (M89 c h4 h3 h10 h1 h0 h7 h6).symm
              · exact (L434 c h6 h4 h10 h0 h7 h3 h1).trans (M434 c h6 h4 h10 h0 h7 h3 h1).symm
    · cases h6 : c.b6
      · cases h7 : c.b7
        · cases h10 : c.b10
          · cases h4 : c.b4
            · cases h16 : c.b16
              · cases h2 : c.b2
                · cases h15 : c.b15
                  · exact (L281 c h10 h15 h4 h6 h0 h7 h2 h1 h16).trans (M281 c h10 h15 h4 h6 h0 h7 h2 h1 h16).symm
                  · cases h13 : c.b13
                    · exact (L457 c h13 h15 h6 h1 h2 h10 h7 h0 h16 h4).trans (M457 c h13 h15 h6 h1 h2 h10 h7 h0 h16 h4).symm
                    · exact (L364 c h2 h13 h16 h0 h7 h6 h1 h10 h15 h4).trans (M364 c h2 h13 h16 h0 h7 h6 h1 h10 h15 h4).symm
                · exact (L260 c h2 h4 h0 h6 h16 h7 h1 h10).trans (M260 c h2 h4 h0 h6 h16 h7 h1 h10).symm
              · cases h9 : c.b9
                · cases h14 : c.b14
                  · cases h2 : c.b2
                    · cases h8 : c.b8
                      · cases h11 : c.b11
                        · exact (L375 c h4 h11 h10 h6 h14 h1 h8 h0 h2 h7 h16 h9).trans (M375 c h4 h11 h10 h6 h14 h1 h8 h0 h2 h7 h16 h9).symm
                        · cases h3 : c.b3
                          · exact (L26 c h7 h8 h3 h4 h0 h6 h16 h10 h1 h9 h2 h11 h14).trans (M26 c h7 h8 h3 h4 h0 h6 h16 h10 h1 h9 h2 h11 h14).symm
                          · exact (L173 c h2 h6 h11 h9 h14 h0 h1 h3 h4 h8 h7 h10 h16).trans (M173 c h2 h6 h11 h9 h14 h0 h1 h3 h4 h8 h7 h10 h16).symm
                      · exact (L199 c h10 h2 h1 h8 h9 h0 h4 h14 h6 h16 h7).trans (M199 c h10 h2 h1 h8 h9 h0 h4 h14 h6 h16 h7).symm
                    · cases h5 : c.b5
                      · cases h15 : c.b15
                        · cases h8 : c.b8
                          · exact (L232 c h2 h15 h0 h5 h14 h6 h9 h4 h8 h10 h7 h16 h1).trans (M232 c h2 h15 h0 h5 h14 h6 h9 h4 h8 h10 h7 h16 h1).symm
                          · exact (L154 c h16 h9 h4 h0 h1 h6 h14 h2 h5 h15 h8 h10 h7).trans (M154 c h16 h9 h4 h0 h1 h6 h14 h2 h5 h15 h8 h10 h7).symm
                        · cases h11 : c.b11
                          · exact (L267 c h7 h6 h1 h16 h0 h11 h10 h14 h9 h2 h4 h5 h15).trans (M267 c h7 h6 h1 h16 h0 h11 h10 h14 h9 h2 h4 h5 h15).symm
                          · exact (L137 c h10 h4 h9 h1 h14 h16 h11 h7 h2 h15 h0 h5 h6).trans (M137 c h10 h4 h9 h1 h14 h16 h11 h7 h2 h15 h0 h5 h6).symm
                      · exact (L402 c h9 h2 h5 h14 h1 h0 h4 h7 h10 h6 h16).trans (M402 c h9 h2 h5 h14 h1 h0 h4 h7 h10 h6 h16).symm
                  · cases h13 : c.b13
                    · exact (L46 c h6 h7 h10 h0 h9 h16 h14 h13 h1 h4).trans (M46 c h6 h7 h10 h0 h9 h16 h14 h13 h1 h4).symm
                    · cases h3 : c.b3
                      · exact (L10 c h3 h16 h13 h7 h14 h4 h6 h1 h10 h9 h0).trans (M10 c h3 h16 h13 h7 h14 h4 h6 h1 h10 h9 h0).symm
                      · exact (L88 c h10 h1 h4 h3 h0 h16 h6 h14 h9 h13 h7).trans (M88 c h10 h1 h4 h3 h0 h16 h6 h14 h9 h13 h7).symm
                · cases h2 : c.b2
                  · exact (L111 c h10 h2 h1 h16 h6 h7 h0 h4 h9).trans (M111 c h10 h2 h1 h16 h6 h7 h0 h4 h9).symm
                  · exact (L443 c h7 h9 h1 h10 h2 h6 h16 h0 h4).trans (M443 c h7 h9 h1 h10 h2 h6 h16 h0 h4).symm
            · cases h14 : c.b14
              · cases h16 : c.b16
                · cases h8 : c.b8
                  · cases h5 : c.b5
                    · exact (L422 c h14 h4 h7 h8 h16 h1 h6 h5 h0 h10).trans (M422 c h14 h4 h7 h8 h16 h1 h6 h5 h0 h10).symm
                    · exact (L279 c h6 h16 h8 h4 h7 h10 h0 h1 h14 h5).trans (M279 c h6 h16 h8 h4 h7 h10 h0 h1 h14 h5).symm
                  · exact (L18 c h0 h8 h16 h14 h4 h1 h6 h7 h10).trans (M18 c h0 h8 h16 h14 h4 h1 h6 h7 h10).symm
                · exact (L205 c h4 h6 h14 h16 h1 h10 h0 h7).trans (M205 c h4 h6 h14 h16 h1 h10 h0 h7).symm
              · exact (L478 c h7 h0 h14 h4 h6 h10 h1).trans (M478 c h7 h0 h14 h4 h6 h10 h1).symm
          · cases h12 : c.b12
            · cases h8 : c.b8
              · cases h16 : c.b16
                · exact (L250 c h16 h8 h7 h10 h12 h6 h1 h0).trans (M250 c h16 h8 h7 h10 h12 h6 h1 h0).symm
                · exact (L6 c h16 h10 h0 h6 h12 h8 h1 h7).trans (M6 c h16 h10 h0 h6 h12 h8 h1 h7).symm
              · cases h14 : c.b14
                · cases h9 : c.b9
                  · exact (L302 c h7 h9 h12 h0 h14 h10 h6 h8 h1).trans (M302 c h7 h9 h12 h0 h14 h10 h6 h8 h1).symm
                  · exact (L450 c h7 h12 h0 h1 h14 h10 h9 h6 h8).trans (M450 c h7 h12 h0 h1 h14 h10 h9 h6 h8).symm
                · exact (L132 c h14 h12 h7 h8 h6 h0 h10 h1).trans (M132 c h14 h12 h7 h8 h6 h0 h10 h1).symm
            · cases h13 : c.b13
              · exact (L484 c h12 h1 h13 h10 h7 h0 h6).trans (M484 c h12 h1 h13 h10 h7 h0 h6).symm
              · exact (L401 c h12 h0 h6 h10 h7 h1 h13).trans (M401 c h12 h0 h6 h10 h7 h1 h13).symm
        · cases h14 : c.b14
          · cases h4 : c.b4
            · cases h8 : c.b8
              · cases h10 : c.b10
                · cases h2 : c.b2
                  · exact (L386 c h7 h1 h4 h10 h2 h14 h8 h0 h6).trans (M386 c h7 h1 h4 h10 h2 h14 h8 h0 h6).symm
                  · cases h13 : c.b13
                    · exact (L404 c h13 h10 h14 h0 h7 h1 h6 h2 h8 h4).trans (M404 c h13 h10 h14 h0 h7 h1 h6 h2 h8 h4).symm
                    · cases h12 : c.b12
                      · exact (L417 c h6 h1 h2 h14 h7 h10 h0 h12 h13 h4 h8).trans (M417 c h6 h1 h2 h14 h7 h10 h0 h12 h13 h4 h8).symm
                      · exact (L373 c h4 h13 h0 h12 h7 h14 h1 h2 h8 h10 h6).trans (M373 c h4 h13 h0 h12 h7 h14 h1 h2 h8 h10 h6).symm
                · cases h15 : c.b15
                  · cases h13 : c.b13
                    · exact (L296 c h4 h7 h0 h14 h1 h13 h6 h8 h10 h15).trans (M296 c h4 h7 h0 h14 h1 h13 h6 h8 h10 h15).symm
                    · exact (L295 c h8 h0 h1 h7 h13 h10 h4 h15 h6 h14).trans (M295 c h8 h0 h1 h7 h13 h10 h4 h15 h6 h14).symm
                  · cases h11 : c.b11
                    · cases h5 : c.b5
                      · cases h3 : c.b3
                        · exact (L240 c h11 h14 h4 h7 h15 h1 h6 h0 h5 h3 h10 h8).trans (M240 c h11 h14 h4 h7 h15 h1 h6 h0 h5 h3 h10 h8).symm
                        · cases h13 : c.b13
                          · exact (L408 c h14 h15 h11 h0 h5 h1 h13 h3 h10 h8 h4 h7 h6).trans (M408 c h14 h15 h11 h0 h5 h1 h13 h3 h10 h8 h4 h7 h6).symm
                          · cases h16 : c.b16
                            · exact (L248 c h1 h7 h5 h3 h6 h14 h16 h0 h11 h10 h13 h4 h15 h8).trans (M248 c h1 h7 h5 h3 h6 h14 h16 h0 h11 h10 h13 h4 h15 h8).symm
                            · exact (L9 c h3 h5 h1 h6 h8 h7 h16 h4 h13 h14 h10 h11 h15 h0).trans (M9 c h3 h5 h1 h6 h8 h7 h16 h4 h13 h14 h10 h11 h15 h0).symm
                      · cases h12 : c.b12
                        · cases h3 : c.b3
                          · exact (L35 c h12 h7 h3 h4 h15 h10 h0 h6 h14 h5 h1 h11 h8).trans (M35 c h12 h7 h3 h4 h15 h10 h0 h6 h14 h5 h1 h11 h8).symm
                          · cases h9 : c.b9
                            · exact (L339 c h3 h11 h0 h9 h1 h7 h15 h5 h12 h8 h14 h6 h10 h4).trans (M339 c h3 h11 h0 h9 h1 h7 h15 h5 h12 h8 h14 h6 h10 h4).symm
                            · cases h16 : c.b16
                              · exact (L14 c h9 h7 h11 h10 h16 h1 h5 h14 h15 h0 h4 h3 h8 h12 h6).trans (M14 c h9 h7 h11 h10 h16 h1 h5 h14 h15 h0 h4 h3 h8 h12 h6).symm
                              · exact (L13 c h7 h9 h10 h11 h12 h14 h0 h4 h5 h1 h6 h3 h16 h15 h8).trans (M13 c h7 h9 h10 h11 h12 h14 h0 h4 h5 h1 h6 h3 h16 h15 h8).symm
                        · cases h16 : c.b16
                          · exact (L356 c h8 h5 h16 h4 h15 h11 h12 h14 h1 h7 h6 h0 h10).trans (M356 c h8 h5 h16 h4 h15 h11 h12 h14 h1 h7 h6 h0 h10).symm
                          · exact (L429 c h15 h8 h1 h11 h5 h6 h0 h12 h14 h7 h4 h16 h10).trans (M429 c h15 h8 h1 h11 h5 h6 h0 h12 h14 h7 h4 h16 h10).symm
                    · cases h2 : c.b2
                      · exact (L161 c h6 h0 h8 h2 h15 h1 h7 h11 h10 h4 h14).trans (M161 c h6 h0 h8 h2 h15 h1 h7 h11 h10 h4 h14).symm
                      · exact (L346 c h1 h8 h7 h0 h6 h2 h14 h15 h4 h11 h10).trans (M346 c h1 h8 h7 h0 h6 h2 h14 h15 h4 h11 h10).symm
              · cases h16 : c.b16
                · exact (L198 c h6 h4 h14 h8 h16 h1 h7 h0).trans (M198 c h6 h4 h14 h8 h16 h1 h7 h0).symm
                · exact (L495 c h6 h0 h16 h7 h4 h14 h1 h8).trans (M495 c h6 h0 h16 h7 h4 h14 h1 h8).symm
            · cases h3 : c.b3
              · cases h12 : c.b12
                · cases h15 : c.b15
                  · cases h10 : c.b10
                    · exact (L48 c h0 h1 h15 h6 h3 h10 h4 h7 h14 h12).trans (M48 c h0 h1 h15 h6 h3 h10 h4 h7 h14 h12).symm
                    · cases h2 : c.b2
                      · exact (L283 c h12 h3 h2 h10 h6 h0 h1 h14 h15 h4 h7).trans (M283 c h12 h3 h2 h10 h6 h0 h1 h14 h15 h4 h7).symm
                      · cases h13 : c.b13
                        · exact (L96 c h15 h2 h10 h7 h12 h13 h3 h4 h14 h1 h6 h0).trans (M96 c h15 h2 h10 h7 h12 h13 h3 h4 h14 h1 h6 h0).symm
                        · exact (L453 c h13 h3 h10 h7 h4 h14 h2 h15 h12 h1 h0 h6).trans (M453 c h13 h3 h10 h7 h4 h14 h2 h15 h12 h1 h0 h6).symm
                  · cases h13 : c.b13
                    · cases h9 : c.b9
                      · exact (L255 c h13 h6 h12 h14 h1 h7 h0 h3 h4 h15 h9).trans (M255 c h13 h6 h12 h14 h1 h7 h0 h3 h4 h15 h9).symm
                      · exact (L287 c h6 h4 h12 h13 h7 h14 h1 h0 h15 h3 h9).trans (M287 c h6 h4 h12 h13 h7 h14 h1 h0 h15 h3 h9).symm
                    · exact (L293 c h7 h4 h3 h14 h1 h6 h15 h12 h13 h0).trans (M293 c h7 h4 h3 h14 h1 h6 h15 h12 h13 h0).symm
                · cases h16 : c.b16
                  · cases h15 : c.b15
                    · cases h5 : c.b5
                      · cases h13 : c.b13
                        · cases h8 : c.b8
                          · cases h2 : c.b2
                            · exact (L97 c h0 h15 h7 h16 h4 h1 h5 h3 h8 h2 h6 h13 h14 h12).trans (M97 c h0 h15 h7 h16 h4 h1 h5 h3 h8 h2 h6 h13 h14 h12).symm
                            · exact (L466 c h8 h5 h14 h15 h7 h16 h1 h3 h13 h12 h2 h6 h4 h0).trans (M466 c h8 h5 h14 h15 h7 h16 h1 h3 h13 h12 h2 h6 h4 h0).symm
                          · exact (L338 c h13 h4 h6 h0 h8 h15 h5 h14 h7 h1 h12 h16 h3).trans (M338 c h13 h4 h6 h0 h8 h15 h5 h14 h7 h1 h12 h16 h3).symm
                        · exact (L371 c h0 h3 h5 h4 h14 h12 h15 h6 h7 h16 h13 h1).trans (M371 c h0 h3 h5 h4 h14 h12 h15 h6 h7 h16 h13 h1).symm
                      · exact (L204 c h16 h5 h14 h3 h6 h0 h1 h15 h4 h12 h7).trans (M204 c h16 h5 h14 h3 h6 h0 h1 h15 h4 h12 h7).symm
                    · cases h2 : c.b2
                      · exact (L428 c h7 h6 h14 h0 h2 h16 h1 h4 h3 h15 h12).trans (M428 c h7 h6 h14 h0 h2 h16 h1 h4 h3 h15 h12).symm
                      · exact (L367 c h1 h16 h3 h12 h7 h4 h6 h14 h0 h15 h2).trans (M367 c h1 h16 h3 h12 h7 h4 h6 h14 h0 h15 h2).symm
                  · exact (L468 c h16 h1 h4 h3 h7 h6 h14 h0 h12).trans (M468 c h16 h1 h4 h3 h7 h6 h14 h0 h12).symm
              · cases h5 : c.b5
                · exact (L66 c h4 h0 h14 h7 h3 h5 h6 h1).trans (M66 c h4 h0 h14 h7 h3 h5 h6 h1).symm
                · exact (L113 c h0 h5 h3 h7 h6 h14 h1 h4).trans (M113 c h0 h5 h3 h7 h6 h14 h1 h4).symm
          · cases h15 : c.b15
            · exact (L187 c h6 h15 h14 h1 h7 h0).trans (M187 c h6 h15 h14 h1 h7 h0).symm
            · cases h4 : c.b4
              · exact (L72 c h14 h0 h7 h4 h15 h6 h1).trans (M72 c h14 h0 h7 h4 h15 h6 h1).symm
              · exact (L37 c h6 h1 h7 h0 h14 h15 h4).trans (M37 c h6 h1 h7 h0 h14 h15 h4).symm
      · cases h10 : c.b10
        · exact (L500 c h10 h1 h0 h6).trans (M500 c h10 h1 h0 h6).symm
        · cases h14 : c.b14
          · cases h9 : c.b9
            · cases h11 : c.b11
              · cases h17 : c.b17
                · cases h16 : c.b16
                  · exact (L99 c h9 h14 h16 h10 h0 h6 h11 h17 h1).trans (M99 c h9 h14 h16 h10 h0 h6 h11 h17 h1).symm
                  · exact (L15 c h14 h9 h16 h6 h17 h11 h1 h0 h10).trans (M15 c h14 h9 h16 h6 h17 h11 h1 h0 h10).symm
                · cases h3 : c.b3
                  · exact (L455 c h1 h9 h17 h6 h14 h11 h10 h3 h0).trans (M455 c h1 h9 h17 h6 h14 h11 h10 h3 h0).symm
                  · exact (L317 c h3 h1 h11 h10 h0 h17 h9 h14 h6).trans (M317 c h3 h1 h11 h10 h0 h17 h9 h14 h6).symm
              · cases h16 : c.b16
                · cases h5 : c.b5
                  · exact (L39 c h5 h10 h1 h16 h0 h11 h14 h6 h9).trans (M39 c h5 h10 h1 h16 h0 h11 h14 h6 h9).symm
                  · exact (L300 c h10 h5 h11 h1 h9 h14 h16 h0 h6).trans (M300 c h10 h5 h11 h1 h9 h14 h16 h0 h6).symm
                · cases h3 : c.b3
                  · cases h12 : c.b12
                    · exact (L398 c h10 h16 h3 h9 h11 h12 h14 h6 h0 h1).trans (M398 c h10 h16 h3 h9 h11 h12 h14 h6 h0 h1).symm
                    · cases h7 : c.b7
                      · exact (L73 c h14 h10 h3 h1 h0 h7 h6 h16 h9 h12 h11).trans (M73 c h14 h10 h3 h1 h0 h7 h6 h16 h9 h12 h11).symm
                      · exact (L74 c h0 h12 h7 h1 h10 h16 h14 h3 h9 h11 h6).trans (M74 c h0 h12 h7 h1 h10 h16 h14 h3 h9 h11 h6).symm
                  · exact (L134 c h16 h6 h14 h10 h1 h11 h9 h0 h3).trans (M134 c h16 h6 h14 h10 h1 h11 h9 h0 h3).symm
            · cases h8 : c.b8
              · cases h2 : c.b2
                · cases h4 : c.b4
                  · cases h3 : c.b3
                    · cases h7 : c.b7
                      · cases h12 : c.b12
                        · exact (L511 c h2 h3 h12 h4 h14 h9 h7 h1 h10 h0 h6 h8).trans (M511 c h2 h3 h12 h4 h14 h9 h7 h1 h10 h0 h6 h8).symm
                        · exact (L5 c h10 h8 h0 h14 h12 h1 h2 h9 h3 h7 h6 h4).trans (M5 c h10 h8 h0 h14 h12 h1 h2 h9 h3 h7 h6 h4).symm
                      · exact (L366 c h6 h2 h7 h1 h0 h10 h14 h4 h9 h3 h8).trans (M366 c h6 h2 h7 h1 h0 h10 h14 h4 h9 h3 h8).symm
                    · exact (L263 c h4 h2 h9 h6 h14 h10 h8 h1 h3 h0).trans (M263 c h4 h2 h9 h6 h14 h10 h8 h1 h3 h0).symm
                  · cases h7 : c.b7
                    · exact (L228 c h1 h10 h9 h8 h2 h7 h6 h4 h14 h0).trans (M228 c h1 h10 h9 h8 h2 h7 h6 h4 h14 h0).symm
                    · exact (L471 c h8 h6 h1 h4 h14 h10 h2 h9 h0 h7).trans (M471 c h8 h6 h1 h4 h14 h10 h2 h9 h0 h7).symm
                · cases h5 : c.b5
                  · cases h7 : c.b7
                    · exact (L60 c h7 h14 h10 h1 h9 h6 h0 h8 h5 h2).trans (M60 c h7 h14 h10 h1 h9 h6 h0 h8 h5 h2).symm
                    · cases h16 : c.b16
                      · cases h3 : c.b3
                        · exact (L251 c h9 h0 h6 h1 h8 h14 h2 h7 h5 h10 h16 h3).trans (M251 c h9 h0 h6 h1 h8 h14 h2 h7 h5 h10 h16 h3).symm
                        · cases h17 : c.b17
                          · exact (L217 c h8 h5 h17 h9 h10 h0 h3 h16 h7 h2 h14 h1 h6).trans (M217 c h8 h5 h17 h9 h10 h0 h3 h16 h7 h2 h14 h1 h6).symm
                          · cases h11 : c.b11
                            · exact (L397 c h11 h7 h14 h1 h5 h3 h16 h2 h17 h6 h0 h9 h8 h10).trans (M397 c h11 h7 h14 h1 h5 h3 h16 h2 h17 h6 h0 h9 h8 h10).symm
                            · exact (L416 c h1 h2 h10 h5 h8 h16 h17 h7 h6 h3 h0 h11 h9 h14).trans (M416 c h1 h2 h10 h5 h8 h16 h17 h7 h6 h3 h0 h11 h9 h14).symm
                      · cases h17 : c.b17
                        · exact (L32 c h6 h1 h10 h0 h17 h7 h8 h16 h2 h14 h9 h5).trans (M32 c h6 h1 h10 h0 h17 h7 h8 h16 h2 h14 h9 h5).symm
                        · exact (L395 c h1 h9 h2 h5 h7 h6 h14 h0 h10 h8 h16 h17).trans (M395 c h1 h9 h2 h5 h7 h6 h14 h0 h10 h8 h16 h17).symm
                  · cases h7 : c.b7
                    · exact (L16 c h5 h6 h8 h2 h7 h14 h0 h9 h10 h1).trans (M16 c h5 h6 h8 h2 h7 h14 h0 h9 h10 h1).symm
                    · exact (L458 c h2 h6 h1 h5 h0 h10 h14 h7 h9 h8).trans (M458 c h2 h6 h1 h5 h0 h10 h14 h7 h9 h8).symm
              · cases h7 : c.b7
                · cases h16 : c.b16
                  · cases h11 : c.b11
                    · cases h15 : c.b15
                      · cases h5 : c.b5
                        · cases h4 : c.b4
                          · exact (L44 c h9 h5 h10 h7 h0 h11 h14 h8 h6 h4 h16 h15 h1).trans (M44 c h9 h5 h10 h7 h0 h11 h14 h8 h6 h4 h16 h15 h1).symm
                          · exact (L241 c h16 h6 h8 h1 h0 h9 h11 h10 h5 h14 h15 h4 h7).trans (M241 c h16 h6 h8 h1 h0 h9 h11 h10 h5 h14 h15 h4 h7).symm
                        · cases h12 : c.b12
                          · exact (L7 c h12 h6 h1 h11 h14 h5 h8 h0 h16 h7 h9 h10 h15).trans (M7 c h12 h6 h1 h11 h14 h5 h8 h0 h16 h7 h9 h10 h15).symm
                          · exact (L150 c h12 h5 h1 h10 h7 h15 h11 h14 h0 h6 h8 h9 h16).trans (M150 c h12 h5 h1 h10 h7 h15 h11 h14 h0 h6 h8 h9 h16).symm
                      · exact (L501 c h15 h9 h1 h6 h7 h16 h10 h11 h0 h8 h14).trans (M501 c h15 h9 h1 h6 h7 h16 h10 h11 h0 h8 h14).symm
                    · cases h12 : c.b12
                      · cases h13 : c.b13
                        · exact (L320 c h7 h13 h0 h16 h1 h6 h12 h8 h10 h14 h11 h9).trans (M320 c h7 h13 h0 h16 h1 h6 h12 h8 h10 h14 h11 h9).symm
                        · cases h17 : c.b17
                          · exact (L326 c h9 h17 h7 h12 h0 h16 h14 h10 h1 h13 h8 h6 h11).trans (M326 c h9 h17 h7 h12 h0 h16 h14 h10 h1 h13 h8 h6 h11).symm
                          · cases h15 : c.b15
                            · cases h4 : c.b4
                              · exact (L438 c h17 h15 h10 h16 h9 h11 h14 h1 h8 h4 h7 h12 h6 h0 h13).trans (M438 c h17 h15 h10 h16 h9 h11 h14 h1 h8 h4 h7 h12 h6 h0 h13).symm
                              · exact (L206 c h17 h16 h7 h4 h12 h14 h13 h0 h10 h6 h9 h11 h15 h8 h1).trans (M206 c h17 h16 h7 h4 h12 h14 h13 h0 h10 h6 h9 h11 h15 h8 h1).symm
                            · exact (L509 c h8 h13 h14 h17 h0 h9 h6 h15 h16 h11 h1 h7 h10 h12).trans (M509 c h8 h13 h14 h17 h0 h9 h6 h15 h16 h11 h1 h7 h10 h12).symm
                      · cases h13 : c.b13
                        · exact (L207 c h7 h9 h10 h0 h6 h8 h1 h11 h13 h14 h12 h16).trans (M207 c h7 h9 h10 h0 h6 h8 h1 h11 h13 h14 h12 h16).symm
                        · cases h17 : c.b17
                          · exact (L506 c h13 h10 h16 h0 h8 h9 h1 h11 h14 h7 h12 h6 h17).trans (M506 c h13 h10 h16 h0 h8 h9 h1 h11 h14 h7 h12 h6 h17).symm
                          · cases h5 : c.b5
                            · exact (L175 c h14 h0 h11 h10 h12 h8 h1 h5 h17 h13 h9 h6 h16 h7).trans (M175 c h14 h0 h11 h10 h12 h8 h1 h5 h17 h13 h9 h6 h16 h7).symm
                            · exact (L24 c h8 h0 h12 h1 h13 h17 h10 h7 h6 h9 h11 h14 h5 h16).trans (M24 c h8 h0 h12 h1 h13 h17 h10 h7 h6 h9 h11 h14 h5 h16).symm
                  · exact (L436 c h16 h9 h0 h10 h14 h8 h1 h6 h7).trans (M436 c h16 h9 h0 h10 h14 h8 h1 h6 h7).symm
                · cases h13 : c.b13
                  · cases h3 : c.b3
                    · cases h17 : c.b17
                      · exact (L380 c h0 h1 h13 h10 h6 h8 h17 h3 h14 h7 h9).trans (M380 c h0 h1 h13 h10 h6 h8 h17 h3 h14 h7 h9).symm
                      · cases h2 : c.b2
                        · exact (L347 c h2 h9 h10 h3 h6 h7 h14 h8 h13 h1 h17 h0).trans (M347 c h2 h9 h10 h3 h6 h7 h14 h8 h13 h1 h17 h0).symm
                        · exact (L183 c h7 h17 h8 h0 h2 h6 h3 h10 h9 h14 h1 h13).trans (M183 c h7 h17 h8 h0 h2 h6 h3 h10 h9 h14 h1 h13).symm
                    · cases h11 : c.b11
                      · exact (L171 c h11 h3 h8 h10 h9 h13 h0 h7 h6 h14 h1).trans (M171 c h11 h3 h8 h10 h9 h13 h0 h7 h6 h14 h1).symm
                      · cases h2 : c.b2
                        · exact (L191 c h8 h13 h9 h7 h11 h0 h6 h2 h3 h10 h14 h1).trans (M191 c h8 h13 h9 h7 h11 h0 h6 h2 h3 h10 h14 h1).symm
                        · exact (L223 c h8 h11 h0 h6 h3 h10 h7 h1 h13 h2 h9 h14).trans (M223 c h8 h11 h0 h6 h3 h10 h7 h1 h13 h2 h9 h14).symm
                  · cases h4 : c.b4
                    · cases h11 : c.b11
                      · cases h12 : c.b12
                        · exact (L227 c h12 h1 h9 h11 h4 h0 h8 h13 h10 h7 h14 h6).trans (M227 c h12 h1 h9 h11 h4 h0 h8 h13 h10 h7 h14 h6).symm
                        · cases h3 : c.b3
                          · exact (L145 c h12 h0 h11 h3 h10 h8 h6 h1 h14 h4 h13 h7 h9).trans (M145 c h12 h0 h11 h3 h10 h8 h6 h1 h14 h4 h13 h7 h9).symm
                          · exact (L472 c h9 h6 h13 h11 h7 h12 h8 h1 h14 h3 h0 h10 h4).trans (M472 c h9 h6 h13 h11 h7 h12 h8 h1 h14 h3 h0 h10 h4).symm
                      · cases h12 : c.b12
                        · cases h3 : c.b3
                          · exact (L69 c h0 h8 h4 h10 h1 h6 h14 h12 h11 h9 h13 h3 h7).trans (M69 c h0 h8 h4 h10 h1 h6 h14 h12 h11 h9 h13 h3 h7).symm
                          · cases h16 : c.b16
                            · cases h2 : c.b2
                              · exact (L34 c h3 h4 h11 h12 h2 h1 h13 h7 h10 h14 h16 h6 h0 h8 h9).trans (M34 c h3 h4 h11 h12 h2 h1 h13 h7 h10 h14 h16 h6 h0 h8 h9).symm
                              · cases h5 : c.b5
                                · exact (L17 c h13 h2 h16 h0 h12 h8 h3 h11 h14 h4 h1 h10 h7 h6 h5 h9).trans (M17 c h13 h2 h16 h0 h12 h8 h3 h11 h14 h4 h1 h10 h7 h6 h5 h9).symm
                                · exact (L56 c h14 h4 h8 h12 h13 h16 h2 h6 h5 h3 h10 h7 h11 h1 h0 h9).trans (M56 c h14 h4 h8 h12 h13 h16 h2 h6 h5 h3 h10 h7 h11 h1 h0 h9).symm
                            · exact (L430 c h7 h14 h12 h13 h10 h4 h0 h6 h9 h11 h8 h16 h1 h3).trans (M430 c h7 h14 h12 h13 h10 h4 h0 h6 h9 h11 h8 h16 h1 h3).symm
                        · exact (L505 c h11 h1 h9 h8 h7 h10 h12 h4 h13 h0 h6 h14).trans (M505 c h11 h1 h9 h8 h7 h10 h12 h4 h13 h0 h6 h14).symm
                    · cases h11 : c.b11
                      · exact (L461 c h9 h13 h1 h10 h11 h4 h0 h7 h14 h8 h6).trans (M461 c h9 h13 h1 h10 h11 h4 h0 h7 h14 h8 h6).symm
                      · cases h12 : c.b12
                        · cases h17 : c.b17
                          · exact (L476 c h17 h8 h12 h13 h11 h1 h9 h0 h10 h4 h6 h14 h7).trans (M476 c h17 h8 h12 h13 h11 h1 h9 h0 h10 h4 h6 h14 h7).symm
                          · cases h3 : c.b3
                            · cases h2 : c.b2
                              · exact (L274 c h8 h3 h2 h4 h12 h6 h11 h7 h9 h0 h1 h13 h14 h10 h17).trans (M274 c h8 h3 h2 h4 h12 h6 h11 h7 h9 h0 h1 h13 h14 h10 h17).symm
                              · exact (L200 c h7 h0 h13 h10 h17 h4 h8 h9 h14 h11 h12 h2 h1 h6 h3).trans (M200 c h7 h0 h13 h10 h17 h4 h8 h9 h14 h11 h12 h2 h1 h6 h3).symm
                            · exact (L168 c h12 h0 h1 h7 h9 h11 h14 h4 h6 h17 h10 h3 h8 h13).trans (M168 c h12 h0 h1 h7 h9 h11 h14 h4 h6 h17 h10 h3 h8 h13).symm
                        · exact (L21 c h1 h11 h10 h8 h7 h0 h12 h4 h14 h9 h6 h13).trans (M21 c h1 h11 h10 h8 h7 h0 h12 h4 h14 h9 h6 h13).symm
          · cases h2 : c.b2
            · exact (L393 c h1 h14 h0 h6 h10 h2).trans (M393 c h1 h14 h0 h6 h10 h2).symm
            · exact (L92 c h14 h0 h10 h2 h6 h1).trans (M92 c h14 h0 h10 h2 h6 h1).symm

end TblComplete
