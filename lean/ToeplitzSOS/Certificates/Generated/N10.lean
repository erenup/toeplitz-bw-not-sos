import ToeplitzSOS.Certificates.Basic
import ToeplitzSOS.ThmA.Main

/-! Exact rational residual-form certificate.
The generator is untrusted. Lean proves each exact polynomial identity. -/

namespace ToeplitzSOS

noncomputable section

set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

private def hGramBlock0 : MvPolynomial (ThmA.HV 9) ℝ :=
  MvPolynomial.C (71 : ℝ) * (Certificates.hWedge (0 : Fin 9) (1 : Fin 9)) * (Certificates.hWedge (0 : Fin 9) (1 : Fin 9)) +
  MvPolynomial.C (-2 : ℝ) * (Certificates.hWedge (0 : Fin 9) (1 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (2 : Fin 9)) +
  MvPolynomial.C ((4387 : ℝ) / 250) * (Certificates.hWedge (0 : Fin 9) (1 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (3 : Fin 9)) +
  MvPolynomial.C ((97 : ℝ) / 250) * (Certificates.hWedge (0 : Fin 9) (1 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (4 : Fin 9)) +
  MvPolynomial.C ((-6753 : ℝ) / 500) * (Certificates.hWedge (0 : Fin 9) (1 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((-1184 : ℝ) / 125) * (Certificates.hWedge (0 : Fin 9) (1 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((1311 : ℝ) / 500) * (Certificates.hWedge (0 : Fin 9) (1 : Fin 9)) * (Certificates.hWedge (6 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((827 : ℝ) / 500) * (Certificates.hWedge (0 : Fin 9) (1 : Fin 9)) * (Certificates.hWedge (7 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (54 : ℝ) * (Certificates.hWedge (1 : Fin 9) (2 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (2 : Fin 9)) +
  MvPolynomial.C (-4 : ℝ) * (Certificates.hWedge (1 : Fin 9) (2 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (3 : Fin 9)) +
  MvPolynomial.C ((2047 : ℝ) / 500) * (Certificates.hWedge (1 : Fin 9) (2 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (4 : Fin 9)) +
  MvPolynomial.C ((-1149 : ℝ) / 125) * (Certificates.hWedge (1 : Fin 9) (2 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((-1558 : ℝ) / 125) * (Certificates.hWedge (1 : Fin 9) (2 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((19 : ℝ) / 250) * (Certificates.hWedge (1 : Fin 9) (2 : Fin 9)) * (Certificates.hWedge (6 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((161 : ℝ) / 50) * (Certificates.hWedge (1 : Fin 9) (2 : Fin 9)) * (Certificates.hWedge (7 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((4887 : ℝ) / 250) * (Certificates.hWedge (1 : Fin 9) (2 : Fin 9)) * (Certificates.hWedge (0 : Fin 9) (3 : Fin 9)) +
  MvPolynomial.C (39 : ℝ) * (Certificates.hWedge (2 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (3 : Fin 9)) +
  MvPolynomial.C (-6 : ℝ) * (Certificates.hWedge (2 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (4 : Fin 9)) +
  MvPolynomial.C ((-4393 : ℝ) / 500) * (Certificates.hWedge (2 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((-1031 : ℝ) / 100) * (Certificates.hWedge (2 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-312 : ℝ) / 125) * (Certificates.hWedge (2 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (6 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((193 : ℝ) / 50) * (Certificates.hWedge (2 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (7 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((443 : ℝ) / 100) * (Certificates.hWedge (2 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (0 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((4047 : ℝ) / 500) * (Certificates.hWedge (2 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (4 : Fin 9)) +
  MvPolynomial.C (26 : ℝ) * (Certificates.hWedge (3 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (4 : Fin 9)) +
  MvPolynomial.C (-8 : ℝ) * (Certificates.hWedge (3 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((-3369 : ℝ) / 500) * (Certificates.hWedge (3 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-789 : ℝ) / 250) * (Certificates.hWedge (3 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (6 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((264 : ℝ) / 125) * (Certificates.hWedge (3 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (7 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((453 : ℝ) / 500) * (Certificates.hWedge (3 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (0 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((933 : ℝ) / 250) * (Certificates.hWedge (3 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-1393 : ℝ) / 500) * (Certificates.hWedge (3 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C (16 : ℝ) * (Certificates.hWedge (4 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C (-6 : ℝ) * (Certificates.hWedge (4 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-1483 : ℝ) / 500) * (Certificates.hWedge (4 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (6 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((82 : ℝ) / 125) * (Certificates.hWedge (4 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (7 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((393 : ℝ) / 100) * (Certificates.hWedge (4 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((-37 : ℝ) / 250) * (Certificates.hWedge (4 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((-369 : ℝ) / 500) * (Certificates.hWedge (4 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C (9 : ℝ) * (Certificates.hWedge (5 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C (-4 : ℝ) * (Certificates.hWedge (5 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (6 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((-337 : ℝ) / 500) * (Certificates.hWedge (5 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (7 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((157 : ℝ) / 125) * (Certificates.hWedge (5 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((517 : ℝ) / 500) * (Certificates.hWedge (5 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C (4 : ℝ) * (Certificates.hWedge (6 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (6 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C (-2 : ℝ) * (Certificates.hWedge (6 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (7 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((663 : ℝ) / 500) * (Certificates.hWedge (6 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (1 : ℝ) * (Certificates.hWedge (7 : Fin 9) (8 : Fin 9)) * (Certificates.hWedge (7 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (53 : ℝ) * (Certificates.hWedge (0 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (0 : Fin 9) (3 : Fin 9)) +
  MvPolynomial.C ((-1097 : ℝ) / 250) * (Certificates.hWedge (0 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (4 : Fin 9)) +
  MvPolynomial.C ((-643 : ℝ) / 100) * (Certificates.hWedge (0 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C (-2 : ℝ) * (Certificates.hWedge (0 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-547 : ℝ) / 500) * (Certificates.hWedge (0 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((297 : ℝ) / 250) * (Certificates.hWedge (0 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (35 : ℝ) * (Certificates.hWedge (0 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (0 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((-5753 : ℝ) / 500) * (Certificates.hWedge (0 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (4 : Fin 9)) +
  MvPolynomial.C ((684 : ℝ) / 125) * (Certificates.hWedge (0 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((239 : ℝ) / 250) * (Certificates.hWedge (0 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((-1297 : ℝ) / 250) * (Certificates.hWedge (0 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (38 : ℝ) * (Certificates.hWedge (1 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (4 : Fin 9)) +
  MvPolynomial.C ((149 : ℝ) / 125) * (Certificates.hWedge (1 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((-1933 : ℝ) / 250) * (Certificates.hWedge (1 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C (-4 : ℝ) * (Certificates.hWedge (1 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((193 : ℝ) / 100) * (Certificates.hWedge (1 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (17 : ℝ) * (Certificates.hWedge (0 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (0 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((2311 : ℝ) / 500) * (Certificates.hWedge (0 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-739 : ℝ) / 250) * (Certificates.hWedge (0 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((-2827 : ℝ) / 500) * (Certificates.hWedge (0 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (22 : ℝ) * (Certificates.hWedge (1 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-1058 : ℝ) / 125) * (Certificates.hWedge (1 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((-2019 : ℝ) / 250) * (Certificates.hWedge (1 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((-644 : ℝ) / 125) * (Certificates.hWedge (1 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (25 : ℝ) * (Certificates.hWedge (2 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((-169 : ℝ) / 100) * (Certificates.hWedge (2 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-963 : ℝ) / 250) * (Certificates.hWedge (2 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C (-2 : ℝ) * (Certificates.hWedge (2 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (7 : ℝ) * (Certificates.hWedge (1 : Fin 9) (8 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((261 : ℝ) / 50) * (Certificates.hWedge (1 : Fin 9) (8 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((394 : ℝ) / 125) * (Certificates.hWedge (1 : Fin 9) (8 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C (12 : ℝ) * (Certificates.hWedge (2 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((188 : ℝ) / 125) * (Certificates.hWedge (2 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-393 : ℝ) / 50) * (Certificates.hWedge (2 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (15 : ℝ) * (Certificates.hWedge (3 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-1211 : ℝ) / 250) * (Certificates.hWedge (3 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((-407 : ℝ) / 125) * (Certificates.hWedge (3 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (5 : ℝ) * (Certificates.hWedge (3 : Fin 9) (8 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((514 : ℝ) / 125) * (Certificates.hWedge (3 : Fin 9) (8 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C (8 : ℝ) * (Certificates.hWedge (4 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((-582 : ℝ) / 125) * (Certificates.hWedge (4 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (3 : ℝ) * (Certificates.hWedge (5 : Fin 9) (8 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (8 : Fin 9))

private theorem hGramBlock0_sos : IsSumSqHomQuad hGramBlock0 := by
  let d : Fin 20 → NNReal := ![
    (71 : NNReal),
    ((3833 : NNReal) / 71),
    ((18135126237 : NNReal) / 479125000),
    ((310610008843185907 : NNReal) / 12090084158000000),
    ((12982112460031497561041 : NNReal) / 931830026529557721000),
    ((262594062958825126256794759 : NNReal) / 51928449840125990244164000),
    ((2061573863154155244468414409 : NNReal) / 1103336398986660194356280500),
    ((35449677113291915086427449769851 : NNReal) / 61331822428836118522935328667750),
    ((888291421525301580383364963103086529 : NNReal) / 17724838556645957543213724884925500),
    ((4938043470269928096012272250386997794411 : NNReal) / 142126627444048252861338394096493844640),
    ((553499498671637988808246113728307944452928647 : NNReal) / 15431385844593525300038350782459368107534375),
    ((470059530941081915183798840000606240572602370483 : NNReal) / 27674974933581899440412305686415397222646432350),
    ((199802968530262123302193582536956323240081939417492777 : NNReal) / 9401190618821638303675976800012124811452047409660000),
    ((38110204653644674587131219707780957378683158390040053736247 : NNReal) / 1598423748242096986417548660295650585920655515339942216000),
    ((447269218651700885648738739157888589647837223936477529370181793 : NNReal) / 76220409307289349174262439415561914757366316780080107472494000),
    ((743722383038916211493632528718173566686938237612005219136253591011 : NNReal) / 74544869775283480941456456526314764941306203989412921561696965500),
    ((3924965399182794808862121847081823969037149431106159532974822354681812 : NNReal) / 278895893639593579310112198269315087507601839104501957176095096629125),
    ((1224635560855614271899778461065565414398270662174922424427616107626673033 : NNReal) / 490620674897849351107765230885227996129643678888269941621852794335226500),
    ((224063544132985228205349918619022222117383021927039277268686738604189423557403 : NNReal) / 39188337947379656700792910754098093260744661189597517581683715444053537056000),
    ((143992889954508696583919615910079828382356433726229079054899013439759854585087631 : NNReal) / 112031772066492614102674959309511111058691510963519638634343369302094711778701500)]
  let terms : Fin 20 → List (ℝ × Fin 9 × Fin 9) := ![
    [((1 : ℝ), (0 : Fin 9), (1 : Fin 9)), (((-1 : ℝ) / 71), (1 : Fin 9), (2 : Fin 9)), (((4387 : ℝ) / 35500), (2 : Fin 9), (3 : Fin 9)), (((97 : ℝ) / 35500), (3 : Fin 9), (4 : Fin 9)), (((-6753 : ℝ) / 71000), (4 : Fin 9), (5 : Fin 9)), (((-592 : ℝ) / 8875), (5 : Fin 9), (6 : Fin 9)), (((1311 : ℝ) / 71000), (6 : Fin 9), (7 : Fin 9)), (((827 : ℝ) / 71000), (7 : Fin 9), (8 : Fin 9))],
    [(((346977 : ℝ) / 1916500), (0 : Fin 9), (3 : Fin 9)), ((1 : ℝ), (1 : Fin 9), (2 : Fin 9)), (((-66613 : ℝ) / 1916500), (2 : Fin 9), (3 : Fin 9)), (((145531 : ℝ) / 3833000), (3 : Fin 9), (4 : Fin 9)), (((-333069 : ℝ) / 3833000), (4 : Fin 9), (5 : Fin 9)), (((-55901 : ℝ) / 479125), (5 : Fin 9), (6 : Fin 9)), (((4009 : ℝ) / 3833000), (6 : Fin 9), (7 : Fin 9)), (((115137 : ℝ) / 3833000), (7 : Fin 9), (8 : Fin 9))],
    [(((108512577 : ℝ) / 12090084158), (0 : Fin 9), (3 : Fin 9)), (((1061261875 : ℝ) / 18135126237), (0 : Fin 9), (5 : Fin 9)), (((646339625 : ℝ) / 6045042079), (1 : Fin 9), (4 : Fin 9)), ((1 : ℝ), (2 : Fin 9), (3 : Fin 9)), (((-1886302467 : ℝ) / 24180168316), (3 : Fin 9), (4 : Fin 9)), (((-3566159327 : ℝ) / 36270252474), (4 : Fin 9), (5 : Fin 9)), (((-2294369197 : ℝ) / 18135126237), (5 : Fin 9), (6 : Fin 9)), (((-674630746 : ℝ) / 18135126237), (6 : Fin 9), (7 : Fin 9)), (((902751071 : ℝ) / 18135126237), (7 : Fin 9), (8 : Fin 9))],
    [(((-4166201978948106 : ℝ) / 310610008843185907), (0 : Fin 9), (3 : Fin 9)), (((2089079982202500 : ℝ) / 310610008843185907), (0 : Fin 9), (5 : Fin 9)), (((5476808123574000 : ℝ) / 310610008843185907), (0 : Fin 9), (7 : Fin 9)), (((3816933041974500 : ℝ) / 310610008843185907), (1 : Fin 9), (4 : Fin 9)), (((22560097038828000 : ℝ) / 310610008843185907), (1 : Fin 9), (6 : Fin 9)), (((-16841487232094000 : ℝ) / 310610008843185907), (2 : Fin 9), (5 : Fin 9)), ((1 : ℝ), (3 : Fin 9), (4 : Fin 9)), (((-49493834878517576 : ℝ) / 310610008843185907), (4 : Fin 9), (5 : Fin 9)), (((-42200148659240892 : ℝ) / 310610008843185907), (5 : Fin 9), (6 : Fin 9)), (((-20475382565438522 : ℝ) / 310610008843185907), (6 : Fin 9), (7 : Fin 9)), (((13772469073887410 : ℝ) / 310610008843185907), (7 : Fin 9), (8 : Fin 9))],
    [(((771374054714945906394 : ℝ) / 12982112460031497561041), (0 : Fin 9), (3 : Fin 9)), (((457186482882276045545 : ℝ) / 25964224920062995122082), (0 : Fin 9), (5 : Fin 9)), (((67262121599905385784 : ℝ) / 12982112460031497561041), (0 : Fin 9), (7 : Fin 9)), (((835319953148790589761 : ℝ) / 25964224920062995122082), (1 : Fin 9), (4 : Fin 9)), (((277066487649941390448 : ℝ) / 12982112460031497561041), (1 : Fin 9), (6 : Fin 9)), (((1831046002130580921765 : ℝ) / 12982112460031497561041), (1 : Fin 9), (8 : Fin 9)), (((-206834735957324950104 : ℝ) / 12982112460031497561041), (2 : Fin 9), (5 : Fin 9)), (((-68955421963187271354 : ℝ) / 12982112460031497561041), (2 : Fin 9), (7 : Fin 9)), (((-343845279789406799049 : ℝ) / 12982112460031497561041), (3 : Fin 9), (6 : Fin 9)), ((1 : ℝ), (4 : Fin 9), (5 : Fin 9)), (((-9364513796204095512797 : ℝ) / 25964224920062995122082), (5 : Fin 9), (6 : Fin 9)), (((-3283214652235064840513 : ℝ) / 25964224920062995122082), (6 : Fin 9), (7 : Fin 9)), (((1704025583844869080135 : ℝ) / 25964224920062995122082), (7 : Fin 9), (8 : Fin 9))],
    [(((74521981457581679411975748 : ℝ) / 262594062958825126256794759), (0 : Fin 9), (3 : Fin 9)), (((20365582116677212173303845 : ℝ) / 262594062958825126256794759), (0 : Fin 9), (5 : Fin 9)), (((649697095937589845872704 : ℝ) / 37513437565546446608113537), (0 : Fin 9), (7 : Fin 9)), (((37209711433947032806031901 : ℝ) / 262594062958825126256794759), (1 : Fin 9), (4 : Fin 9)), (((2676235719689939630018688 : ℝ) / 37513437565546446608113537), (1 : Fin 9), (6 : Fin 9)), (((196805022561936338851830 : ℝ) / 1404246325983022065544357), (1 : Fin 9), (8 : Fin 9)), (((-1997854425256208952098624 : ℝ) / 37513437565546446608113537), (2 : Fin 9), (5 : Fin 9)), (((-7411486854749765432588 : ℝ) / 1404246325983022065544357), (2 : Fin 9), (7 : Fin 9)), (((-36957279045981938440878 : ℝ) / 1404246325983022065544357), (3 : Fin 9), (6 : Fin 9)), (((32611066499599121873334992 : ℝ) / 262594062958825126256794759), (3 : Fin 9), (8 : Fin 9)), (((2440637142485921541475708 : ℝ) / 23872187541711375114254069), (4 : Fin 9), (7 : Fin 9)), ((1 : ℝ), (5 : Fin 9), (6 : Fin 9)), (((-1287121746709706377857905 : ℝ) / 2206672797973320388712561), (6 : Fin 9), (7 : Fin 9)), (((32729819938769129365461381 : ℝ) / 262594062958825126256794759), (7 : Fin 9), (8 : Fin 9))],
    [(((9327184138407814983256257 : ℝ) / 18913521680313350866682701), (0 : Fin 9), (3 : Fin 9)), (((390102193626717847734105395 : ℝ) / 2061573863154155244468414409), (0 : Fin 9), (5 : Fin 9)), (((99381248530146411536362737 : ℝ) / 2061573863154155244468414409), (0 : Fin 9), (7 : Fin 9)), (((712751050838522406221184891 : ℝ) / 2061573863154155244468414409), (1 : Fin 9), (4 : Fin 9)), (((409371765468550119043825314 : ℝ) / 2061573863154155244468414409), (1 : Fin 9), (6 : Fin 9)), (((1460511954739336801049807235 : ℝ) / 4123147726308310488936828818), (1 : Fin 9), (8 : Fin 9)), (((-305602823846565013841397997 : ℝ) / 2061573863154155244468414409), (2 : Fin 9), (5 : Fin 9)), (((-27500734007814484294576523 : ℝ) / 2061573863154155244468414409), (2 : Fin 9), (7 : Fin 9)), (((-274264076996852559586452351 : ℝ) / 4123147726308310488936828818), (3 : Fin 9), (6 : Fin 9)), (((404156228466847802647382170 : ℝ) / 2061573863154155244468414409), (3 : Fin 9), (8 : Fin 9)), (((665441943048918197352536885 : ℝ) / 4123147726308310488936828818), (4 : Fin 9), (7 : Fin 9)), (((1463024065056311417716427943 : ℝ) / 4123147726308310488936828818), (5 : Fin 9), (8 : Fin 9)), ((1 : ℝ), (6 : Fin 9), (7 : Fin 9)), (((-428673160017445697029231065 : ℝ) / 2061573863154155244468414409), (7 : Fin 9), (8 : Fin 9))],
    [(((-20658076656806913502026112347960 : ℝ) / 35449677113291915086427449769851), (0 : Fin 9), (3 : Fin 9)), (((-26835356882861941485177198800515 : ℝ) / 141798708453167660345709799079404), (0 : Fin 9), (5 : Fin 9)), (((-1043251844877827447149228661412 : ℝ) / 35449677113291915086427449769851), (0 : Fin 9), (7 : Fin 9)), (((-49030559505617280898651071578187 : ℝ) / 141798708453167660345709799079404), (1 : Fin 9), (4 : Fin 9)), (((-4297368526582838888257087598664 : ℝ) / 35449677113291915086427449769851), (1 : Fin 9), (6 : Fin 9)), (((-4886489903315759340237299743890 : ℝ) / 35449677113291915086427449769851), (1 : Fin 9), (8 : Fin 9)), (((3208056997604445107900387473172 : ℝ) / 35449677113291915086427449769851), (2 : Fin 9), (5 : Fin 9)), (((184020484908583303398249456004 : ℝ) / 35449677113291915086427449769851), (2 : Fin 9), (7 : Fin 9)), (((917615661233341066945324990074 : ℝ) / 35449677113291915086427449769851), (3 : Fin 9), (6 : Fin 9)), (((-129215168307002912326827765798 : ℝ) / 35449677113291915086427449769851), (3 : Fin 9), (8 : Fin 9)), (((-212752363104205432079522149419 : ℝ) / 70899354226583830172854899539702), (4 : Fin 9), (7 : Fin 9)), (((33821026305896413158515243335305 : ℝ) / 141798708453167660345709799079404), (5 : Fin 9), (8 : Fin 9)), ((1 : ℝ), (7 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (0 : Fin 9), (3 : Fin 9)), (((-6762780363409230685616473916191050 : ℝ) / 888291421525301580383364963103086529), (0 : Fin 9), (5 : Fin 9)), (((-1371890776537784939577574880807262 : ℝ) / 888291421525301580383364963103086529), (0 : Fin 9), (7 : Fin 9)), (((-51244490886155793641995955259298637 : ℝ) / 888291421525301580383364963103086529), (1 : Fin 9), (4 : Fin 9)), (((-5651099755009948559054646197762364 : ℝ) / 888291421525301580383364963103086529), (1 : Fin 9), (6 : Fin 9)), (((-24485440508360850624234221791529685 : ℝ) / 1776582843050603160766729926206173058), (1 : Fin 9), (8 : Fin 9)), (((-105533432220703112208905920727666921 : ℝ) / 1776582843050603160766729926206173058), (2 : Fin 9), (5 : Fin 9)), (((461049007027659782746395015921933 : ℝ) / 888291421525301580383364963103086529), (2 : Fin 9), (7 : Fin 9)), (((-30851647826989037793632321097548479 : ℝ) / 1776582843050603160766729926206173058), (3 : Fin 9), (6 : Fin 9)), (((-6382557557752458481174820808133758 : ℝ) / 888291421525301580383364963103086529), (3 : Fin 9), (8 : Fin 9)), (((-14949917036596837239143293432126148 : ℝ) / 888291421525301580383364963103086529), (4 : Fin 9), (7 : Fin 9)), (((12314500237811618352418973834294253 : ℝ) / 1776582843050603160766729926206173058), (5 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (0 : Fin 9), (5 : Fin 9)), (((-4542739309556073932792738166353007432 : ℝ) / 4938043470269928096012272250386997794411), (0 : Fin 9), (7 : Fin 9)), (((-22162836733307214319649292408970337806553 : ℝ) / 123451086756748202400306806259674944860275), (1 : Fin 9), (4 : Fin 9)), (((9253649421387490233100135040393627545776 : ℝ) / 123451086756748202400306806259674944860275), (1 : Fin 9), (6 : Fin 9)), (((-4774293083119154406240743080288147980 : ℝ) / 705434781467132585144610321483856827773), (1 : Fin 9), (8 : Fin 9)), (((10490399860999622835496113777179622672 : ℝ) / 4938043470269928096012272250386997794411), (2 : Fin 9), (5 : Fin 9)), (((1729877368656831099840992599727773970848 : ℝ) / 123451086756748202400306806259674944860275), (2 : Fin 9), (7 : Fin 9)), (((5193781622107335218199501260627898276 : ℝ) / 4938043470269928096012272250386997794411), (3 : Fin 9), (6 : Fin 9)), (((-9647409554235240707992551137847313881264 : ℝ) / 123451086756748202400306806259674944860275), (3 : Fin 9), (8 : Fin 9)), (((-73840712508895347703525449596097408938 : ℝ) / 24690217351349640480061361251934988972055), (4 : Fin 9), (7 : Fin 9)), (((-68733612322240343783936095746070531593 : ℝ) / 24690217351349640480061361251934988972055), (5 : Fin 9), (8 : Fin 9))],
    [(((-2084012622553450349249709563748091353332175 : ℝ) / 1106998997343275977616492227456615888905857294), (0 : Fin 9), (7 : Fin 9)), ((1 : ℝ), (1 : Fin 9), (4 : Fin 9)), (((3287452244816742405819000558002581285560951 : ℝ) / 553499498671637988808246113728307944452928647), (1 : Fin 9), (6 : Fin 9)), (((-61982264734011975290170292968053437305720875 : ℝ) / 4427995989373103910465968909826463555623429176), (1 : Fin 9), (8 : Fin 9)), (((75771771098218426654093600163400300001577225 : ℝ) / 4427995989373103910465968909826463555623429176), (2 : Fin 9), (5 : Fin 9)), (((3232007029110731980342187348678056431575621 : ℝ) / 1106998997343275977616492227456615888905857294), (2 : Fin 9), (7 : Fin 9)), (((-472912963348982203135852074274014779543975375 : ℝ) / 4427995989373103910465968909826463555623429176), (3 : Fin 9), (6 : Fin 9)), (((-44724937158863555887213364476033759694408631 : ℝ) / 2213997994686551955232984454913231777811714588), (3 : Fin 9), (8 : Fin 9)), (((-138600326720985932562969969110534921890234385 : ℝ) / 2213997994686551955232984454913231777811714588), (4 : Fin 9), (7 : Fin 9)), (((97047948959157924548176757797944015237276205 : ℝ) / 4427995989373103910465968909826463555623429176), (5 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (0 : Fin 9), (7 : Fin 9)), (((1246849364987533460383949525061420903908134925809 : ℝ) / 9401190618821638303675976800012124811452047409660), (1 : Fin 9), (6 : Fin 9)), (((-3194726295213054488919752358799457853402486889943 : ℝ) / 18802381237643276607351953600024249622904094819320), (1 : Fin 9), (8 : Fin 9)), (((-1589768431452090690702937215603970795059393320407 : ℝ) / 18802381237643276607351953600024249622904094819320), (2 : Fin 9), (5 : Fin 9)), (((78062592046729176597507193233394442261934114 : ℝ) / 470059530941081915183798840000606240572602370483), (2 : Fin 9), (7 : Fin 9)), (((2353915227972719531817871311005570232323154963 : ℝ) / 18802381237643276607351953600024249622904094819320), (3 : Fin 9), (6 : Fin 9)), (((-18273559293534831791107440498679674100363997079 : ℝ) / 9401190618821638303675976800012124811452047409660), (3 : Fin 9), (8 : Fin 9)), (((-4036050125057066347756625218287270600075655419 : ℝ) / 2350297654705409575918994200003031202863011852415), (4 : Fin 9), (7 : Fin 9)), (((-5751153118013596144783551765244181851758016029 : ℝ) / 3760476247528655321470390720004849924580818963864), (5 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (1 : Fin 9), (6 : Fin 9)), (((3109581820868285652579275732372596515306849521498921 : ℝ) / 399605937060524246604387165073912646480163878834985554), (1 : Fin 9), (8 : Fin 9)), (((-73013094541681505110823529858486653926392988178381191 : ℝ) / 399605937060524246604387165073912646480163878834985554), (2 : Fin 9), (5 : Fin 9)), (((-38230202850709199656833236473272152266546917840530400 : ℝ) / 199802968530262123302193582536956323240081939417492777), (2 : Fin 9), (7 : Fin 9)), (((1091636177551223793027877556543227956294679688599299 : ℝ) / 399605937060524246604387165073912646480163878834985554), (3 : Fin 9), (6 : Fin 9)), (((-23351437781709824132771435934620713943259216609404647 : ℝ) / 199802968530262123302193582536956323240081939417492777), (3 : Fin 9), (8 : Fin 9)), (((-727152545836890262512062200731844237372891748538588 : ℝ) / 199802968530262123302193582536956323240081939417492777), (4 : Fin 9), (7 : Fin 9)), (((-2006314892781457673042232960559871188350746909326305 : ℝ) / 399605937060524246604387165073912646480163878834985554), (5 : Fin 9), (8 : Fin 9))],
    [(((-114059116596348340263232817357967475766747012621391338901 : ℝ) / 38110204653644674587131219707780957378683158390040053736247), (1 : Fin 9), (8 : Fin 9)), ((1 : ℝ), (2 : Fin 9), (5 : Fin 9)), (((-1199802141491697379183143224686832897615820900434580790980 : ℝ) / 38110204653644674587131219707780957378683158390040053736247), (2 : Fin 9), (7 : Fin 9)), (((-1363743838759227644714534761395504738369152776521773691289 : ℝ) / 38110204653644674587131219707780957378683158390040053736247), (3 : Fin 9), (6 : Fin 9)), (((-594478242579989643628865191245936238140795323030037500906 : ℝ) / 38110204653644674587131219707780957378683158390040053736247), (3 : Fin 9), (8 : Fin 9)), (((-3007695463491376528890861117456226027583656721608511082526 : ℝ) / 38110204653644674587131219707780957378683158390040053736247), (4 : Fin 9), (7 : Fin 9)), (((-1484134108197645324702101696999240312408294013312619361949 : ℝ) / 38110204653644674587131219707780957378683158390040053736247), (5 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (1 : Fin 9), (8 : Fin 9)), (((67795937162164768104155578691769860595109497468127084034518098 : ℝ) / 149089739550566961882912913052629529882612407978825843123393931), (2 : Fin 9), (7 : Fin 9)), (((123840763700127140572396743991257705104595986023083123044486993 : ℝ) / 447269218651700885648738739157888589647837223936477529370181793), (3 : Fin 9), (6 : Fin 9)), (((-18211560676715957940444195584744013216342028342218182820634856 : ℝ) / 447269218651700885648738739157888589647837223936477529370181793), (3 : Fin 9), (8 : Fin 9)), (((-5926393797153861101195908909159941349626161841774728542043857 : ℝ) / 149089739550566961882912913052629529882612407978825843123393931), (4 : Fin 9), (7 : Fin 9)), (((-5261024213031359247015010047211635704276505778351409597205519 : ℝ) / 149089739550566961882912913052629529882612407978825843123393931), (5 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (2 : Fin 9), (7 : Fin 9)), (((308461918429804339452728192287510413406956471119068530985382556 : ℝ) / 743722383038916211493632528718173566686938237612005219136253591011), (3 : Fin 9), (6 : Fin 9)), (((-317542997933924940055672506160129567686666885143874097002672493556 : ℝ) / 743722383038916211493632528718173566686938237612005219136253591011), (3 : Fin 9), (8 : Fin 9)), (((3522012926550160309744137715072286757625794974358140650217719559 : ℝ) / 743722383038916211493632528718173566686938237612005219136253591011), (4 : Fin 9), (7 : Fin 9)), (((3841035621116043853112688665138297374633659343633489636893136708 : ℝ) / 743722383038916211493632528718173566686938237612005219136253591011), (5 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (3 : Fin 9), (6 : Fin 9)), (((1503889761622094543426007077174280214752205799444632925162897110916 : ℝ) / 981241349795698702215530461770455992259287357776539883243705588670453), (3 : Fin 9), (8 : Fin 9)), (((-5901868847563499935555234805177174103050129317326818643365352491342019 : ℝ) / 31399723193462358470896974776654591752297195448849276263798578837454496), (4 : Fin 9), (7 : Fin 9)), (((-410811419033100677101138886373592018200051972447491927432754585504483 : ℝ) / 3924965399182794808862121847081823969037149431106159532974822354681812), (5 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (3 : Fin 9), (8 : Fin 9)), (((907359012629236908868304327786696274816407952639465986473881124883744463 : ℝ) / 1224635560855614271899778461065565414398270662174922424427616107626673033), (4 : Fin 9), (7 : Fin 9)), (((-63699538535568724761197303015975171664032478945187009531512037192119668 : ℝ) / 1224635560855614271899778461065565414398270662174922424427616107626673033), (5 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (4 : Fin 9), (7 : Fin 9)), (((-103561863436267961733429926310684053897160254754214032529120310268795242877128 : ℝ) / 224063544132985228205349918619022222117383021927039277268686738604189423557403), (5 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (5 : Fin 9), (8 : Fin 9))]]
  apply Certificates.weightedHWedgeSOS d terms
  simp [Fin.sum_univ_succ, hGramBlock0, d, terms, Certificates.hWedgeForm]
  polynomial

private def hGramBlock1 : MvPolynomial (ThmA.HV 9) ℝ :=
  MvPolynomial.C (62 : ℝ) * (Certificates.hWedge (0 : Fin 9) (2 : Fin 9)) * (Certificates.hWedge (0 : Fin 9) (2 : Fin 9)) +
  MvPolynomial.C ((-5387 : ℝ) / 250) * (Certificates.hWedge (0 : Fin 9) (2 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (3 : Fin 9)) +
  MvPolynomial.C (-2 : ℝ) * (Certificates.hWedge (0 : Fin 9) (2 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (4 : Fin 9)) +
  MvPolynomial.C ((243 : ℝ) / 100) * (Certificates.hWedge (0 : Fin 9) (2 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((-11 : ℝ) / 250) * (Certificates.hWedge (0 : Fin 9) (2 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-1239 : ℝ) / 250) * (Certificates.hWedge (0 : Fin 9) (2 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((1227 : ℝ) / 500) * (Certificates.hWedge (0 : Fin 9) (2 : Fin 9)) * (Certificates.hWedge (6 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (46 : ℝ) * (Certificates.hWedge (1 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (3 : Fin 9)) +
  MvPolynomial.C ((-6047 : ℝ) / 500) * (Certificates.hWedge (1 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (4 : Fin 9)) +
  MvPolynomial.C (-4 : ℝ) * (Certificates.hWedge (1 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((-67 : ℝ) / 250) * (Certificates.hWedge (1 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-181 : ℝ) / 50) * (Certificates.hWedge (1 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((144 : ℝ) / 125) * (Certificates.hWedge (1 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (6 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((597 : ℝ) / 250) * (Certificates.hWedge (1 : Fin 9) (3 : Fin 9)) * (Certificates.hWedge (0 : Fin 9) (4 : Fin 9)) +
  MvPolynomial.C (32 : ℝ) * (Certificates.hWedge (2 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (4 : Fin 9)) +
  MvPolynomial.C ((-1607 : ℝ) / 500) * (Certificates.hWedge (2 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C (-6 : ℝ) * (Certificates.hWedge (2 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-1037 : ℝ) / 250) * (Certificates.hWedge (2 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((119 : ℝ) / 500) * (Certificates.hWedge (2 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (6 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((489 : ℝ) / 250) * (Certificates.hWedge (2 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (0 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-649 : ℝ) / 125) * (Certificates.hWedge (2 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C (20 : ℝ) * (Certificates.hWedge (3 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((-2631 : ℝ) / 500) * (Certificates.hWedge (3 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C (-4 : ℝ) * (Certificates.hWedge (3 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((-93 : ℝ) / 125) * (Certificates.hWedge (3 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (6 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((797 : ℝ) / 250) * (Certificates.hWedge (3 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (0 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((19 : ℝ) / 50) * (Certificates.hWedge (3 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((-431 : ℝ) / 100) * (Certificates.hWedge (3 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C (12 : ℝ) * (Certificates.hWedge (4 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-2517 : ℝ) / 500) * (Certificates.hWedge (4 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C (-2 : ℝ) * (Certificates.hWedge (4 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (6 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((1119 : ℝ) / 500) * (Certificates.hWedge (4 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((211 : ℝ) / 250) * (Certificates.hWedge (4 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C (6 : ℝ) * (Certificates.hWedge (5 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (5 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((-1663 : ℝ) / 500) * (Certificates.hWedge (5 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (6 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((332 : ℝ) / 125) * (Certificates.hWedge (5 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (2 : ℝ) * (Certificates.hWedge (6 : Fin 9) (8 : Fin 9)) * (Certificates.hWedge (6 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (44 : ℝ) * (Certificates.hWedge (0 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (0 : Fin 9) (4 : Fin 9)) +
  MvPolynomial.C ((4753 : ℝ) / 500) * (Certificates.hWedge (0 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((-989 : ℝ) / 250) * (Certificates.hWedge (0 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-1453 : ℝ) / 500) * (Certificates.hWedge (0 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C (-2 : ℝ) * (Certificates.hWedge (0 : Fin 9) (4 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (26 : ℝ) * (Certificates.hWedge (0 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (0 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-934 : ℝ) / 125) * (Certificates.hWedge (0 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((-3311 : ℝ) / 500) * (Certificates.hWedge (0 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((-3227 : ℝ) / 500) * (Certificates.hWedge (0 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (30 : ℝ) * (Certificates.hWedge (1 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (5 : Fin 9)) +
  MvPolynomial.C ((558 : ℝ) / 125) * (Certificates.hWedge (1 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-219 : ℝ) / 50) * (Certificates.hWedge (1 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((-593 : ℝ) / 100) * (Certificates.hWedge (1 : Fin 9) (5 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (8 : ℝ) * (Certificates.hWedge (0 : Fin 9) (8 : Fin 9)) * (Certificates.hWedge (0 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((1827 : ℝ) / 500) * (Certificates.hWedge (0 : Fin 9) (8 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((2227 : ℝ) / 500) * (Certificates.hWedge (0 : Fin 9) (8 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C (14 : ℝ) * (Certificates.hWedge (1 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (1 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((1019 : ℝ) / 250) * (Certificates.hWedge (1 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-361 : ℝ) / 50) * (Certificates.hWedge (1 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (18 : ℝ) * (Certificates.hWedge (2 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (6 : Fin 9)) +
  MvPolynomial.C ((-688 : ℝ) / 125) * (Certificates.hWedge (2 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((-2119 : ℝ) / 500) * (Certificates.hWedge (2 : Fin 9) (6 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (6 : ℝ) * (Certificates.hWedge (2 : Fin 9) (8 : Fin 9)) * (Certificates.hWedge (2 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C ((293 : ℝ) / 50) * (Certificates.hWedge (2 : Fin 9) (8 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C (10 : ℝ) * (Certificates.hWedge (3 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (3 : Fin 9) (7 : Fin 9)) +
  MvPolynomial.C ((-764 : ℝ) / 125) * (Certificates.hWedge (3 : Fin 9) (7 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (8 : Fin 9)) +
  MvPolynomial.C (4 : ℝ) * (Certificates.hWedge (4 : Fin 9) (8 : Fin 9)) * (Certificates.hWedge (4 : Fin 9) (8 : Fin 9))

private theorem hGramBlock1_sos : IsSumSqHomQuad hGramBlock1 := by
  let d : Fin 16 → NNReal := ![
    (62 : NNReal),
    ((683980231 : NNReal) / 15500000),
    ((42553031927 : NNReal) / 1367960462),
    ((34380911823494121 : NNReal) / 1736858446000000),
    ((4761774655527855575693 : NNReal) / 421166169837802982250),
    ((86121873824832589257655511 : NNReal) / 19047098622111422302772000),
    ((9361306354774128197022691029 : NNReal) / 8612187382483258925765551100),
    ((28580949159093411149321697920444 : NNReal) / 650090719081536680348797988125),
    ((371027519739836844468963373941848583 : NNReal) / 14290474579546705574660848960222000),
    ((191758242995026575234367851492905656029613 : NNReal) / 6678495355317063200441340730953274494000),
    ((375589654154702048875100488916508908091220451 : NNReal) / 47939560748756643808591962873226414007403250),
    ((79032337395879464053976832444472371764155007323497 : NNReal) / 6009434466475232782001607822664142529459527216000),
    ((173542214042564594806822935951771583106783101414149363 : NNReal) / 10537644986117261873863577659262982901887334309799600),
    ((600658954300952140686173308213969091698919563783789712653 : NNReal) / 144618511702137162339019113293142985922319251178457802500),
    ((2197587714761479897808883373798225276153403763675269055757969 : NNReal) / 300329477150476070343086654106984545849459781891894856326500),
    ((485416572090556745869216910677236062283247126511709831888549599 : NNReal) / 403638559854149368985305109473143418068992528021988193914729000)]
  let terms : Fin 16 → List (ℝ × Fin 9 × Fin 9) := ![
    [((1 : ℝ), (0 : Fin 9), (2 : Fin 9)), (((-5387 : ℝ) / 31000), (1 : Fin 9), (3 : Fin 9)), (((-1 : ℝ) / 62), (2 : Fin 9), (4 : Fin 9)), (((243 : ℝ) / 12400), (3 : Fin 9), (5 : Fin 9)), (((-11 : ℝ) / 31000), (4 : Fin 9), (6 : Fin 9)), (((-1239 : ℝ) / 31000), (5 : Fin 9), (7 : Fin 9)), (((1227 : ℝ) / 62000), (6 : Fin 9), (8 : Fin 9))],
    [(((18507000 : ℝ) / 683980231), (0 : Fin 9), (4 : Fin 9)), ((1 : ℝ), (1 : Fin 9), (3 : Fin 9)), (((-96422000 : ℝ) / 683980231), (2 : Fin 9), (4 : Fin 9)), (((-5041345 : ℝ) / 124360042), (3 : Fin 9), (5 : Fin 9)), (((-2136257 : ℝ) / 683980231), (4 : Fin 9), (6 : Fin 9)), (((-34729493 : ℝ) / 683980231), (5 : Fin 9), (7 : Fin 9)), (((24465849 : ℝ) / 1367960462), (6 : Fin 9), (8 : Fin 9))],
    [(((230255736 : ℝ) / 42553031927), (0 : Fin 9), (4 : Fin 9)), (((334466332959 : ℝ) / 10638257981750), (0 : Fin 9), (6 : Fin 9)), (((-443903169919 : ℝ) / 5319128990875), (1 : Fin 9), (5 : Fin 9)), ((1 : ℝ), (2 : Fin 9), (4 : Fin 9)), (((-359496658257 : ℝ) / 6079004561000), (3 : Fin 9), (5 : Fin 9)), (((-2065472568079 : ℝ) / 21276515963500), (4 : Fin 9), (6 : Fin 9)), (((-332391295653 : ℝ) / 4255303192700), (5 : Fin 9), (7 : Fin 9)), (((342056195881 : ℝ) / 42553031927000), (6 : Fin 9), (8 : Fin 9))],
    [(((236500719374000 : ℝ) / 80222127588152949), (0 : Fin 9), (4 : Fin 9)), (((78130607061188 : ℝ) / 26740709196050983), (0 : Fin 9), (6 : Fin 9)), (((2768552362924000 : ℝ) / 34380911823494121), (0 : Fin 9), (8 : Fin 9)), (((-622168883223448 : ℝ) / 80222127588152949), (1 : Fin 9), (5 : Fin 9)), (((330003104740000 : ℝ) / 34380911823494121), (1 : Fin 9), (7 : Fin 9)), (((-3742929951130000 : ℝ) / 34380911823494121), (2 : Fin 9), (6 : Fin 9)), ((1 : ℝ), (3 : Fin 9), (5 : Fin 9)), (((-34221613009184626 : ℝ) / 240666382764458847), (4 : Fin 9), (6 : Fin 9)), (((-2952996383540990 : ℝ) / 26740709196050983), (5 : Fin 9), (7 : Fin 9)), (((-471817687395577 : ℝ) / 26740709196050983), (6 : Fin 9), (8 : Fin 9))],
    [(((11947382884785134013 : ℝ) / 4761774655527855575693), (0 : Fin 9), (4 : Fin 9)), (((43449998929592195106 : ℝ) / 4761774655527855575693), (0 : Fin 9), (6 : Fin 9)), (((95461189489120514227 : ℝ) / 4761774655527855575693), (0 : Fin 9), (8 : Fin 9)), (((-115333534991023863492 : ℝ) / 4761774655527855575693), (1 : Fin 9), (5 : Fin 9)), (((11378686325553888145 : ℝ) / 4761774655527855575693), (1 : Fin 9), (7 : Fin 9)), (((-258116516121775041605 : ℝ) / 9523549311055711151386), (2 : Fin 9), (6 : Fin 9)), (((1885139776194006148551 : ℝ) / 19047098622111422302772), (2 : Fin 9), (8 : Fin 9)), (((355464247343105717019 : ℝ) / 9523549311055711151386), (3 : Fin 9), (7 : Fin 9)), ((1 : ℝ), (4 : Fin 9), (6 : Fin 9)), (((-5174604378075730219551 : ℝ) / 19047098622111422302772), (5 : Fin 9), (7 : Fin 9)), (((-1722551615977868298045 : ℝ) / 19047098622111422302772), (6 : Fin 9), (8 : Fin 9))],
    [(((1674716127944008195877292 : ℝ) / 86121873824832589257655511), (0 : Fin 9), (4 : Fin 9)), (((2110574915448331049119656 : ℝ) / 86121873824832589257655511), (0 : Fin 9), (6 : Fin 9)), (((4525667809240420258533092 : ℝ) / 86121873824832589257655511), (0 : Fin 9), (8 : Fin 9)), (((-5602303149799455422816592 : ℝ) / 86121873824832589257655511), (1 : Fin 9), (5 : Fin 9)), (((28391893408032749426180 : ℝ) / 4532730201306978381981869), (1 : Fin 9), (7 : Fin 9)), (((-6118453029431057501341790 : ℝ) / 86121873824832589257655511), (2 : Fin 9), (6 : Fin 9)), (((5790382299066742115677569 : ℝ) / 86121873824832589257655511), (2 : Fin 9), (8 : Fin 9)), (((2183683047547958152650522 : ℝ) / 86121873824832589257655511), (3 : Fin 9), (7 : Fin 9)), (((25294546970163968818081216 : ℝ) / 86121873824832589257655511), (4 : Fin 9), (8 : Fin 9)), ((1 : ℝ), (5 : Fin 9), (7 : Fin 9)), (((-35631560378313061909069655 : ℝ) / 86121873824832589257655511), (6 : Fin 9), (8 : Fin 9))],
    [(((82605594530702743939722864 : ℝ) / 5200725752652293442790383905), (0 : Fin 9), (4 : Fin 9)), (((693770079820977690742970642 : ℝ) / 15602177257956880328371151715), (0 : Fin 9), (6 : Fin 9)), (((6326856106114440113295055673 : ℝ) / 46806531773870640985113455145), (0 : Fin 9), (8 : Fin 9)), (((-5524623089617356089474698732 : ℝ) / 46806531773870640985113455145), (1 : Fin 9), (5 : Fin 9)), (((150828439167094557280559671 : ℝ) / 9361306354774128197022691029), (1 : Fin 9), (7 : Fin 9)), (((-3421424067421987062522169379 : ℝ) / 18722612709548256394045382058), (2 : Fin 9), (6 : Fin 9)), (((434389057469162222029511415 : ℝ) / 2080290301060917377116153562), (2 : Fin 9), (8 : Fin 9)), (((81908928620190553036842635 : ℝ) / 1040145150530458688558076781), (3 : Fin 9), (7 : Fin 9)), (((4731871218239974621524450184 : ℝ) / 9361306354774128197022691029), (4 : Fin 9), (8 : Fin 9)), ((1 : ℝ), (6 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (0 : Fin 9), (4 : Fin 9)), (((-11238528319220447557610470227 : ℝ) / 57161898318186822298643395840888), (0 : Fin 9), (6 : Fin 9)), (((-3972726867979609386220614789 : ℝ) / 14290474579546705574660848960222), (0 : Fin 9), (8 : Fin 9)), (((24838375553549382561229143701321 : ℝ) / 228647593272747289194573583363552), (1 : Fin 9), (5 : Fin 9)), (((-473537079621157956952269015 : ℝ) / 14290474579546705574660848960222), (1 : Fin 9), (7 : Fin 9)), (((-5100550510148545777141494325105 : ℝ) / 114323796636373644597286791681776), (2 : Fin 9), (6 : Fin 9)), (((-2002987675037635588214247645 : ℝ) / 7145237289773352787330424480111), (2 : Fin 9), (8 : Fin 9)), (((-7580826409187972033664191174285 : ℝ) / 228647593272747289194573583363552), (3 : Fin 9), (7 : Fin 9)), (((-672552091913868009045713049205 : ℝ) / 28580949159093411149321697920444), (4 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (0 : Fin 9), (6 : Fin 9)), (((-818166605030606502364453703879564 : ℝ) / 1113082559219510533406890121825545749), (0 : Fin 9), (8 : Fin 9)), (((-623793361678394370318774983857740383 : ℝ) / 4452330236878042133627560487302182996), (1 : Fin 9), (5 : Fin 9)), (((-142044806994218239042396831419336266 : ℝ) / 1113082559219510533406890121825545749), (1 : Fin 9), (7 : Fin 9)), (((2178887449388989635478499134912351 : ℝ) / 2226165118439021066813780243651091498), (2 : Fin 9), (6 : Fin 9)), (((-46512006457587803770255897198698398 : ℝ) / 371027519739836844468963373941848583), (2 : Fin 9), (8 : Fin 9)), (((-18626196115450105317524349188183 : ℝ) / 44973032695737799329571318053557404), (3 : Fin 9), (7 : Fin 9)), (((-2451386545474917949062004695628442 : ℝ) / 1113082559219510533406890121825545749), (4 : Fin 9), (8 : Fin 9))],
    [(((329280278516603162854787884591782860218 : ℝ) / 191758242995026575234367851492905656029613), (0 : Fin 9), (8 : Fin 9)), ((1 : ℝ), (1 : Fin 9), (5 : Fin 9)), (((-6117641026271498054601724790352236675479 : ℝ) / 383516485990053150468735702985811312059226), (1 : Fin 9), (7 : Fin 9)), (((15895900612160463070488073897150651196315 : ℝ) / 191758242995026575234367851492905656029613), (2 : Fin 9), (6 : Fin 9)), (((-5089010153792720767458928987622772422649 : ℝ) / 383516485990053150468735702985811312059226), (2 : Fin 9), (8 : Fin 9)), (((-13392905457845582492251184045687265190587 : ℝ) / 191758242995026575234367851492905656029613), (3 : Fin 9), (7 : Fin 9)), (((-18094633477361453428169769892973973251918 : ℝ) / 191758242995026575234367851492905656029613), (4 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (0 : Fin 9), (8 : Fin 9)), (((692497903896345876391175494580858865188739719 : ℝ) / 3004717233237616391000803911332071264729763608), (1 : Fin 9), (7 : Fin 9)), (((469000975065140687673463463151120998515307237 : ℝ) / 1502358616618808195500401955666035632364881804), (2 : Fin 9), (6 : Fin 9)), (((-27164531911161344772959063384512138315333207 : ℝ) / 3004717233237616391000803911332071264729763608), (2 : Fin 9), (8 : Fin 9)), (((-1103780408094335866415552760010094946079923 : ℝ) / 375589654154702048875100488916508908091220451), (3 : Fin 9), (7 : Fin 9)), (((-13397273174101814376116328487556481386068367 : ℝ) / 751179308309404097750200977833017816182440902), (4 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (1 : Fin 9), (7 : Fin 9)), (((3089033272585004782634925900155881826260043223306 : ℝ) / 26344112465293154684658944148157457254718335774499), (2 : Fin 9), (6 : Fin 9)), (((-24178003515082107582393043973416614217539876857897 : ℝ) / 79032337395879464053976832444472371764155007323497), (2 : Fin 9), (8 : Fin 9)), (((-62514989363144810568848391017304495002125216784 : ℝ) / 26344112465293154684658944148157457254718335774499), (3 : Fin 9), (7 : Fin 9)), (((-213436131257344622551634730557275115814625170932 : ℝ) / 79032337395879464053976832444472371764155007323497), (4 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (2 : Fin 9), (6 : Fin 9)), (((32745707624275508660267482494885214820943833965998271 : ℝ) / 867711070212822974034114679758857915533915507070746815), (2 : Fin 9), (8 : Fin 9)), (((-45745913987313563000505967577103632385035803512164806 : ℝ) / 289237023404274324678038226586285971844638502356915605), (3 : Fin 9), (7 : Fin 9)), (((-29820945551404505509398637584028877799352201606458818 : ℝ) / 289237023404274324678038226586285971844638502356915605), (4 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (2 : Fin 9), (8 : Fin 9)), (((422694766084980357851723026877640356714108611369492107636 : ℝ) / 600658954300952140686173308213969091698919563783789712653), (3 : Fin 9), (7 : Fin 9)), (((-169618230415220827414946480368990324271879919936715543757 : ℝ) / 3603953725805712844117039849283814550193517382702738275918), (4 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (3 : Fin 9), (7 : Fin 9)), (((-42756861027393791815963540946967799367517765805429424736579 : ℝ) / 89697457745366526441178913216254092904220561782664043092162), (4 : Fin 9), (8 : Fin 9))],
    [((1 : ℝ), (4 : Fin 9), (8 : Fin 9))]]
  apply Certificates.weightedHWedgeSOS d terms
  simp [Fin.sum_univ_succ, hGramBlock1, d, terms, Certificates.hWedgeForm]
  polynomial

/-- A kernel-checked SOS certificate for the residual Hpoly at m = 9. -/
theorem Hpoly_isSumSq_n10 : IsSumSqHomQuad (ThmA.Hpoly 9) := by
  have hgram : ThmA.Hpoly 9 =
      hGramBlock0 +
      hGramBlock1 := by
    simp (config := { maxSteps := 1000000 })
      [Int.Icc_eq_finset_map, Int.Ioc_eq_finset_map,
      Int.Ico_eq_finset_map, Finset.sum_map, Finset.sum_range_succ,
      ThmA.Hpoly, ThmA.Hform, ThmA.hv, ThmA.wedge,
      hGramBlock0, hGramBlock1, Certificates.hWedge]
    polynomial
  rw [hgram]
  exact (hGramBlock0_sos).add hGramBlock1_sos

/-- The residual-form decomposition lifts the checked Hpoly certificate to the original quartic. -/
theorem toeplitzBW_isSumSq_n10 :
    IsSumSqHomQuad (toeplitzBW 10) :=
  ThmA.isSumSqHomQuad_of_Hpoly 10 (by omega) Hpoly_isSumSq_n10

end

end ToeplitzSOS
