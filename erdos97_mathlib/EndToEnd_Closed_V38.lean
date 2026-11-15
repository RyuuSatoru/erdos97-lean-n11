import EndToEnd_Assembly_Core_V34
import Mask_Table_Certificate_V32
import Oriented_Table_Certificate_V33
import Root_000_V34
import Root_001_V34
import Root_002_V34
import Root_003_V34
import Root_004_V34
import Root_005_V34
import Root_006_V34
import Root_007_V34
import Root_008_V34
import Root_009_V34
import Root_010_V34
import Root_011_V34
import Root_012_V34
import Root_013_V34
import Root_014_V34
import Root_015_V34
import Root_016_V34
import Root_017_V34
import Root_018_V34
import Root_019_V34
import Root_020_V34
import Root_021_V34
import Root_022_V34
import Root_023_V34
import Root_024_V34
import Root_025_V34
import Root_026_Parallel_V36
import Root_027_Optimized_V38
import Root_028_V34
import Root_029_V34
import Root_030_V34
import Root_031_V34
import Root_032_V34
import Root_033_V34
import Root_034_V34
import Root_035_V34
import Root_036_V34
import Root_037_V34
import Root_038_V34
import Root_039_V34
import Root_040_V34
import Root_041_V34
import Root_042_V34
import Root_043_V34
import Root_044_V34
import Root_045_V34
import Root_046_V34
import Root_047_V34
import Root_048_V34
import Root_049_V34
import Root_050_V34
import Root_051_V34
import Root_052_V34
import Root_053_V34
import Root_054_V34
import Root_055_V34
import Root_056_V34
import Root_057_V34
import Root_058_V34
import Root_059_V34
import Root_060_V34
import Root_061_V34
import Root_062_V34
import Root_063_V34
import Root_064_V34
import Root_065_V34
import Root_066_V34
import Root_067_V34
import Root_068_V34
import Root_069_V34
import Root_070_V34
import Root_071_V34
import Root_072_V34
import Root_073_V34
import Root_074_V34
import Root_075_V34
import Root_076_V34
import Root_077_V34
import Root_078_V34
import Root_079_V34
import Root_080_V34
import Root_081_V34
import Root_082_V34
import Root_083_V34
import Root_084_V34
import Root_085_V34
import Root_086_V34
import Root_087_V34
import Root_088_V34
import Root_089_V34
import Root_090_V34
import Root_091_V34
import Root_092_V34
import Root_093_V34
import Root_094_V34
import Root_095_V34
import Root_096_V34
import Root_097_V34
import Root_098_V34
import Root_099_V34
import Root_100_V34
import Root_101_V34
import Root_102_V34
import Root_103_V34
import Root_104_V34
import Root_105_V34
import Root_106_V34
import Root_107_V34
import Root_108_V34
import Root_109_V34
import Root_110_V34
import Root_111_V34
import Root_112_V34
import Root_113_V34
import Root_114_V34
import Root_115_V34
import Root_116_V34
import Root_117_V34
import Root_118_V34
import Root_119_V34
import Root_120_V34
import Root_121_V34
import Root_122_V34
import Root_123_V34
import Root_124_V34
import Root_125_V34
import Root_126_V34
import Root_127_V34
import Root_128_V34
import Root_129_V34
import Root_130_V34
import Root_131_V34
import Root_132_V34
import Root_133_V34
import Root_134_V34
import Root_135_V34
import Root_136_V34
import Root_137_V34
import Root_138_V34
import Root_139_V34
import Root_140_V34
import Root_141_V34
import Root_142_V34
import Root_143_V34
import Root_144_V34
import Root_145_V34
import Root_146_V34
import Root_147_V34
import Root_148_V34
import Root_149_V34
import Root_150_V34
import Root_151_V34
import Root_152_V34
import Root_153_V34
import Root_154_V34
import Root_155_V34
import Root_156_V34
import Root_157_V34
import Root_158_V34
import Root_159_V34
import Root_160_V34
import Root_161_V34
import Root_162_V34
import Root_163_V34
import Root_164_V34
import Root_165_V34
import Root_166_V34
import Root_167_V34
import Root_168_V34
import Root_169_V34
import Root_170_V34
import Root_171_V34
import Root_172_V34
import Root_173_V34
import Root_174_V34
import Root_175_V34
import Root_176_V34
import Root_177_V34
import Root_178_V34
import Root_179_V34
import Root_180_V34
import Root_181_V34
import Root_182_V34
import Root_183_V34
import Root_184_V34
import Root_185_V34
import Root_186_V34
import Root_187_V34
import Root_188_V34
import Root_189_V34
import Root_190_V34
import Root_191_V34
import Root_192_V34
import Root_193_V34
import Root_194_V34
import Root_195_V34
import Root_196_V34
import Root_197_V34
import Root_198_V34
import Root_199_V34
import Root_200_V34
import Root_201_V34
import Root_202_V34
import Root_203_V34
import Root_204_V34
import Root_205_V34
import Root_206_V34
import Root_207_V34
import Root_208_V34
import Root_209_V34
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace T34Closed
 theorem all_roots : T34EndToEnd.RootsVerified := by
  intro root
  fin_cases root
  · exact ⟨T34Root000.certificate,T34Root000.accepted⟩
  · exact ⟨T34Root001.certificate,T34Root001.accepted⟩
  · exact ⟨T34Root002.certificate,T34Root002.accepted⟩
  · exact ⟨T34Root003.certificate,T34Root003.accepted⟩
  · exact ⟨T34Root004.certificate,T34Root004.accepted⟩
  · exact ⟨T34Root005.certificate,T34Root005.accepted⟩
  · exact ⟨T34Root006.certificate,T34Root006.accepted⟩
  · exact ⟨T34Root007.certificate,T34Root007.accepted⟩
  · exact ⟨T34Root008.certificate,T34Root008.accepted⟩
  · exact ⟨T34Root009.certificate,T34Root009.accepted⟩
  · exact ⟨T34Root010.certificate,T34Root010.accepted⟩
  · exact ⟨T34Root011.certificate,T34Root011.accepted⟩
  · exact ⟨T34Root012.certificate,T34Root012.accepted⟩
  · exact ⟨T34Root013.certificate,T34Root013.accepted⟩
  · exact ⟨T34Root014.certificate,T34Root014.accepted⟩
  · exact ⟨T34Root015.certificate,T34Root015.accepted⟩
  · exact ⟨T34Root016.certificate,T34Root016.accepted⟩
  · exact ⟨T34Root017.certificate,T34Root017.accepted⟩
  · exact ⟨T34Root018.certificate,T34Root018.accepted⟩
  · exact ⟨T34Root019.certificate,T34Root019.accepted⟩
  · exact ⟨T34Root020.certificate,T34Root020.accepted⟩
  · exact ⟨T34Root021.certificate,T34Root021.accepted⟩
  · exact ⟨T34Root022.certificate,T34Root022.accepted⟩
  · exact ⟨T34Root023.certificate,T34Root023.accepted⟩
  · exact ⟨T34Root024.certificate,T34Root024.accepted⟩
  · exact ⟨T34Root025.certificate,T34Root025.accepted⟩
  · exact ⟨T34Root026.certificate,T34Root026.accepted⟩
  · exact ⟨T34Root027.certificate,T34Root027.accepted⟩
  · exact ⟨T34Root028.certificate,T34Root028.accepted⟩
  · exact ⟨T34Root029.certificate,T34Root029.accepted⟩
  · exact ⟨T34Root030.certificate,T34Root030.accepted⟩
  · exact ⟨T34Root031.certificate,T34Root031.accepted⟩
  · exact ⟨T34Root032.certificate,T34Root032.accepted⟩
  · exact ⟨T34Root033.certificate,T34Root033.accepted⟩
  · exact ⟨T34Root034.certificate,T34Root034.accepted⟩
  · exact ⟨T34Root035.certificate,T34Root035.accepted⟩
  · exact ⟨T34Root036.certificate,T34Root036.accepted⟩
  · exact ⟨T34Root037.certificate,T34Root037.accepted⟩
  · exact ⟨T34Root038.certificate,T34Root038.accepted⟩
  · exact ⟨T34Root039.certificate,T34Root039.accepted⟩
  · exact ⟨T34Root040.certificate,T34Root040.accepted⟩
  · exact ⟨T34Root041.certificate,T34Root041.accepted⟩
  · exact ⟨T34Root042.certificate,T34Root042.accepted⟩
  · exact ⟨T34Root043.certificate,T34Root043.accepted⟩
  · exact ⟨T34Root044.certificate,T34Root044.accepted⟩
  · exact ⟨T34Root045.certificate,T34Root045.accepted⟩
  · exact ⟨T34Root046.certificate,T34Root046.accepted⟩
  · exact ⟨T34Root047.certificate,T34Root047.accepted⟩
  · exact ⟨T34Root048.certificate,T34Root048.accepted⟩
  · exact ⟨T34Root049.certificate,T34Root049.accepted⟩
  · exact ⟨T34Root050.certificate,T34Root050.accepted⟩
  · exact ⟨T34Root051.certificate,T34Root051.accepted⟩
  · exact ⟨T34Root052.certificate,T34Root052.accepted⟩
  · exact ⟨T34Root053.certificate,T34Root053.accepted⟩
  · exact ⟨T34Root054.certificate,T34Root054.accepted⟩
  · exact ⟨T34Root055.certificate,T34Root055.accepted⟩
  · exact ⟨T34Root056.certificate,T34Root056.accepted⟩
  · exact ⟨T34Root057.certificate,T34Root057.accepted⟩
  · exact ⟨T34Root058.certificate,T34Root058.accepted⟩
  · exact ⟨T34Root059.certificate,T34Root059.accepted⟩
  · exact ⟨T34Root060.certificate,T34Root060.accepted⟩
  · exact ⟨T34Root061.certificate,T34Root061.accepted⟩
  · exact ⟨T34Root062.certificate,T34Root062.accepted⟩
  · exact ⟨T34Root063.certificate,T34Root063.accepted⟩
  · exact ⟨T34Root064.certificate,T34Root064.accepted⟩
  · exact ⟨T34Root065.certificate,T34Root065.accepted⟩
  · exact ⟨T34Root066.certificate,T34Root066.accepted⟩
  · exact ⟨T34Root067.certificate,T34Root067.accepted⟩
  · exact ⟨T34Root068.certificate,T34Root068.accepted⟩
  · exact ⟨T34Root069.certificate,T34Root069.accepted⟩
  · exact ⟨T34Root070.certificate,T34Root070.accepted⟩
  · exact ⟨T34Root071.certificate,T34Root071.accepted⟩
  · exact ⟨T34Root072.certificate,T34Root072.accepted⟩
  · exact ⟨T34Root073.certificate,T34Root073.accepted⟩
  · exact ⟨T34Root074.certificate,T34Root074.accepted⟩
  · exact ⟨T34Root075.certificate,T34Root075.accepted⟩
  · exact ⟨T34Root076.certificate,T34Root076.accepted⟩
  · exact ⟨T34Root077.certificate,T34Root077.accepted⟩
  · exact ⟨T34Root078.certificate,T34Root078.accepted⟩
  · exact ⟨T34Root079.certificate,T34Root079.accepted⟩
  · exact ⟨T34Root080.certificate,T34Root080.accepted⟩
  · exact ⟨T34Root081.certificate,T34Root081.accepted⟩
  · exact ⟨T34Root082.certificate,T34Root082.accepted⟩
  · exact ⟨T34Root083.certificate,T34Root083.accepted⟩
  · exact ⟨T34Root084.certificate,T34Root084.accepted⟩
  · exact ⟨T34Root085.certificate,T34Root085.accepted⟩
  · exact ⟨T34Root086.certificate,T34Root086.accepted⟩
  · exact ⟨T34Root087.certificate,T34Root087.accepted⟩
  · exact ⟨T34Root088.certificate,T34Root088.accepted⟩
  · exact ⟨T34Root089.certificate,T34Root089.accepted⟩
  · exact ⟨T34Root090.certificate,T34Root090.accepted⟩
  · exact ⟨T34Root091.certificate,T34Root091.accepted⟩
  · exact ⟨T34Root092.certificate,T34Root092.accepted⟩
  · exact ⟨T34Root093.certificate,T34Root093.accepted⟩
  · exact ⟨T34Root094.certificate,T34Root094.accepted⟩
  · exact ⟨T34Root095.certificate,T34Root095.accepted⟩
  · exact ⟨T34Root096.certificate,T34Root096.accepted⟩
  · exact ⟨T34Root097.certificate,T34Root097.accepted⟩
  · exact ⟨T34Root098.certificate,T34Root098.accepted⟩
  · exact ⟨T34Root099.certificate,T34Root099.accepted⟩
  · exact ⟨T34Root100.certificate,T34Root100.accepted⟩
  · exact ⟨T34Root101.certificate,T34Root101.accepted⟩
  · exact ⟨T34Root102.certificate,T34Root102.accepted⟩
  · exact ⟨T34Root103.certificate,T34Root103.accepted⟩
  · exact ⟨T34Root104.certificate,T34Root104.accepted⟩
  · exact ⟨T34Root105.certificate,T34Root105.accepted⟩
  · exact ⟨T34Root106.certificate,T34Root106.accepted⟩
  · exact ⟨T34Root107.certificate,T34Root107.accepted⟩
  · exact ⟨T34Root108.certificate,T34Root108.accepted⟩
  · exact ⟨T34Root109.certificate,T34Root109.accepted⟩
  · exact ⟨T34Root110.certificate,T34Root110.accepted⟩
  · exact ⟨T34Root111.certificate,T34Root111.accepted⟩
  · exact ⟨T34Root112.certificate,T34Root112.accepted⟩
  · exact ⟨T34Root113.certificate,T34Root113.accepted⟩
  · exact ⟨T34Root114.certificate,T34Root114.accepted⟩
  · exact ⟨T34Root115.certificate,T34Root115.accepted⟩
  · exact ⟨T34Root116.certificate,T34Root116.accepted⟩
  · exact ⟨T34Root117.certificate,T34Root117.accepted⟩
  · exact ⟨T34Root118.certificate,T34Root118.accepted⟩
  · exact ⟨T34Root119.certificate,T34Root119.accepted⟩
  · exact ⟨T34Root120.certificate,T34Root120.accepted⟩
  · exact ⟨T34Root121.certificate,T34Root121.accepted⟩
  · exact ⟨T34Root122.certificate,T34Root122.accepted⟩
  · exact ⟨T34Root123.certificate,T34Root123.accepted⟩
  · exact ⟨T34Root124.certificate,T34Root124.accepted⟩
  · exact ⟨T34Root125.certificate,T34Root125.accepted⟩
  · exact ⟨T34Root126.certificate,T34Root126.accepted⟩
  · exact ⟨T34Root127.certificate,T34Root127.accepted⟩
  · exact ⟨T34Root128.certificate,T34Root128.accepted⟩
  · exact ⟨T34Root129.certificate,T34Root129.accepted⟩
  · exact ⟨T34Root130.certificate,T34Root130.accepted⟩
  · exact ⟨T34Root131.certificate,T34Root131.accepted⟩
  · exact ⟨T34Root132.certificate,T34Root132.accepted⟩
  · exact ⟨T34Root133.certificate,T34Root133.accepted⟩
  · exact ⟨T34Root134.certificate,T34Root134.accepted⟩
  · exact ⟨T34Root135.certificate,T34Root135.accepted⟩
  · exact ⟨T34Root136.certificate,T34Root136.accepted⟩
  · exact ⟨T34Root137.certificate,T34Root137.accepted⟩
  · exact ⟨T34Root138.certificate,T34Root138.accepted⟩
  · exact ⟨T34Root139.certificate,T34Root139.accepted⟩
  · exact ⟨T34Root140.certificate,T34Root140.accepted⟩
  · exact ⟨T34Root141.certificate,T34Root141.accepted⟩
  · exact ⟨T34Root142.certificate,T34Root142.accepted⟩
  · exact ⟨T34Root143.certificate,T34Root143.accepted⟩
  · exact ⟨T34Root144.certificate,T34Root144.accepted⟩
  · exact ⟨T34Root145.certificate,T34Root145.accepted⟩
  · exact ⟨T34Root146.certificate,T34Root146.accepted⟩
  · exact ⟨T34Root147.certificate,T34Root147.accepted⟩
  · exact ⟨T34Root148.certificate,T34Root148.accepted⟩
  · exact ⟨T34Root149.certificate,T34Root149.accepted⟩
  · exact ⟨T34Root150.certificate,T34Root150.accepted⟩
  · exact ⟨T34Root151.certificate,T34Root151.accepted⟩
  · exact ⟨T34Root152.certificate,T34Root152.accepted⟩
  · exact ⟨T34Root153.certificate,T34Root153.accepted⟩
  · exact ⟨T34Root154.certificate,T34Root154.accepted⟩
  · exact ⟨T34Root155.certificate,T34Root155.accepted⟩
  · exact ⟨T34Root156.certificate,T34Root156.accepted⟩
  · exact ⟨T34Root157.certificate,T34Root157.accepted⟩
  · exact ⟨T34Root158.certificate,T34Root158.accepted⟩
  · exact ⟨T34Root159.certificate,T34Root159.accepted⟩
  · exact ⟨T34Root160.certificate,T34Root160.accepted⟩
  · exact ⟨T34Root161.certificate,T34Root161.accepted⟩
  · exact ⟨T34Root162.certificate,T34Root162.accepted⟩
  · exact ⟨T34Root163.certificate,T34Root163.accepted⟩
  · exact ⟨T34Root164.certificate,T34Root164.accepted⟩
  · exact ⟨T34Root165.certificate,T34Root165.accepted⟩
  · exact ⟨T34Root166.certificate,T34Root166.accepted⟩
  · exact ⟨T34Root167.certificate,T34Root167.accepted⟩
  · exact ⟨T34Root168.certificate,T34Root168.accepted⟩
  · exact ⟨T34Root169.certificate,T34Root169.accepted⟩
  · exact ⟨T34Root170.certificate,T34Root170.accepted⟩
  · exact ⟨T34Root171.certificate,T34Root171.accepted⟩
  · exact ⟨T34Root172.certificate,T34Root172.accepted⟩
  · exact ⟨T34Root173.certificate,T34Root173.accepted⟩
  · exact ⟨T34Root174.certificate,T34Root174.accepted⟩
  · exact ⟨T34Root175.certificate,T34Root175.accepted⟩
  · exact ⟨T34Root176.certificate,T34Root176.accepted⟩
  · exact ⟨T34Root177.certificate,T34Root177.accepted⟩
  · exact ⟨T34Root178.certificate,T34Root178.accepted⟩
  · exact ⟨T34Root179.certificate,T34Root179.accepted⟩
  · exact ⟨T34Root180.certificate,T34Root180.accepted⟩
  · exact ⟨T34Root181.certificate,T34Root181.accepted⟩
  · exact ⟨T34Root182.certificate,T34Root182.accepted⟩
  · exact ⟨T34Root183.certificate,T34Root183.accepted⟩
  · exact ⟨T34Root184.certificate,T34Root184.accepted⟩
  · exact ⟨T34Root185.certificate,T34Root185.accepted⟩
  · exact ⟨T34Root186.certificate,T34Root186.accepted⟩
  · exact ⟨T34Root187.certificate,T34Root187.accepted⟩
  · exact ⟨T34Root188.certificate,T34Root188.accepted⟩
  · exact ⟨T34Root189.certificate,T34Root189.accepted⟩
  · exact ⟨T34Root190.certificate,T34Root190.accepted⟩
  · exact ⟨T34Root191.certificate,T34Root191.accepted⟩
  · exact ⟨T34Root192.certificate,T34Root192.accepted⟩
  · exact ⟨T34Root193.certificate,T34Root193.accepted⟩
  · exact ⟨T34Root194.certificate,T34Root194.accepted⟩
  · exact ⟨T34Root195.certificate,T34Root195.accepted⟩
  · exact ⟨T34Root196.certificate,T34Root196.accepted⟩
  · exact ⟨T34Root197.certificate,T34Root197.accepted⟩
  · exact ⟨T34Root198.certificate,T34Root198.accepted⟩
  · exact ⟨T34Root199.certificate,T34Root199.accepted⟩
  · exact ⟨T34Root200.certificate,T34Root200.accepted⟩
  · exact ⟨T34Root201.certificate,T34Root201.accepted⟩
  · exact ⟨T34Root202.certificate,T34Root202.accepted⟩
  · exact ⟨T34Root203.certificate,T34Root203.accepted⟩
  · exact ⟨T34Root204.certificate,T34Root204.accepted⟩
  · exact ⟨T34Root205.certificate,T34Root205.accepted⟩
  · exact ⟨T34Root206.certificate,T34Root206.accepted⟩
  · exact ⟨T34Root207.certificate,T34Root207.accepted⟩
  · exact ⟨T34Root208.certificate,T34Root208.accepted⟩
  · exact ⟨T34Root209.certificate,T34Root209.accepted⟩
theorem no_counterexample :
    ¬ ∃ P : Fin 11 → E97BlockB.XY, E97A1Index.StrictCCW11 P ∧
      E97RowEnumeration15.HasFourEquidistantAtEveryVertex P :=
  T34EndToEnd.no_counterexample_of_roots T32CompleteTable.certified
    T33CompleteTable.certified all_roots
 theorem erdos97_n11_strict_ccw (P : Fin 11 → E97BlockB.XY)
    (hccw : E97A1Index.StrictCCW11 P) :
    ∃ c : Nat, c < 11 ∧ ∀ w : Finset Nat,
      w.card = 4 → w ⊆ Finset.range 11 → c ∉ w → ¬ E97A3.SelectedRowEq P c w :=
  T34EndToEnd.vertex_without_four_of_no_counterexample no_counterexample P hccw
#print axioms T34Closed.all_roots
#print axioms T34Closed.no_counterexample
#print axioms T34Closed.erdos97_n11_strict_ccw
#check T34Closed.erdos97_n11_strict_ccw
end T34Closed
