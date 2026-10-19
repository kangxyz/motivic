# 严格 A1 同伦不变性
# 剩余证明路线图与依赖审计

研究基线：2026-10-17 13:04 UTC（UTC+08:00 为 21:04）。本轮先冻结新实现，复核原典、关键源码声明与匹配的成功检查日志，再确定下阶段工作包。

核心目标：对完美域 k、同伦不变的 Nisnevich 带有限转移层 F，证明项目原定义的所有普通 Nisnevich 上同调在实际投影下同伦不变。

$π*: Hⁿ_Nis(X,F) → Hⁿ_Nis(X×A¹,F)$ 对所有 $n≥0$、所有 $X∈Sm/k$ 为同构。

这份文件是剩余工作的证明合同，不是宣布 strict A1 已完成。已完成的特征零 Milnor 对角比较、任意域上的 Z(1) 普通层复形比较，均保持冻结，不作为 strict A1 的替代结论。

## 摘要：这次调研改变了什么

1. 几何主线收窄为“一次目标端好表示，再通过有限正规化提升源端”。不再默认对 Nisnevich 方块两边独立选择 Bertini 投影，再尝试拼成同一曲线基底。
2. 先证明恰好需要的原截面局部商类提升，不先开发完整 Mayer–Vietoris 复形零同伦或全部 Zariski/Nisnevich 比较。较宽的 MVW 22.2 留作有明确需求时的后备。
3. 单独保留满射与单射两个验收关口。现有代表元交换公式、层切除、全局商群单射，都不能自动充当实际 contractionToBoundary 的同构证明。
4. 高次部分有一项以前容易低估的强度：必须处理 $P=H^q_Nis(-,F)$ 这个通常不是层的同伦不变预层。不能先把 P 层化为零，再进行不与层化交换的开放直像。
5. 普通上同调无同调性的工程路线保持现有“具体短正合步骤＋有限次维数移位”。不为理论上较短的乘积范畴 adjunction 另建一整套依赖乘积的 Abelian/Ext 基础。
6. 高次归纳只需要两个有限阶 Leray 边缘结论。先证明精确 consumer，不把完整谱序列通用框架当作前置大项目。

最关键的仍未证项：目标端好曲线表示的整条相关纤维坏集控制；真实 Nisnevich 边界比较的代表元与非层系数版本；真正 henselian/essentially-smooth 连续性。不能给出可靠完成百分比，也不能把它们称为最后几个小引理。

---
## 1. 最终定理及不变的对象

### 1.1 第一交付目标

输入：`[Field k] [PerfectField k]`，项目原 `SheafWithTransfers k` 对象 F，以及其原 underlying presheaf 的 A1 同伦不变性。输出：原 `F.IsStrictA1Invariant`，即每个次数、每个光滑有限型对象上的实际投影拉回是同构。

最终映射必须与 `Cohomology/A1/Basic.lean` 的定义一致。证明“两个群抽象同构”不够；把普通上同调改成另一种事先定义有转移的群也不够。`HasExt`、必要的 `HasDerivedCategory`、宇宙大小等基础设施实例须在最终应用中显式满足，不能用它们隐含目标的消失性。

### 1.2 范围控制

- 主目标是完美域、整系数。无限域和有限域是两条不同分支；完美不等于无限。
- 可先验收无限完美域版本。有限域须有真实有限扩张、共同缩小、转移和互素次数下降，完成前不得改写成所有完美域。
- 几何 producer 可优先只处理闭点，在允许开集内通过 Jacobson 性和闭特化恢复任意局部点。闭点不是 k-有理点；完美域只保证其有限剩余扩张可分。
- 即使 k 完美，正特征下 k(t) 通常不完美。涉及函数域或剩余域的中间调用，应在原 k 上的有限型光滑模型中展开并取极限，或另证必要 helper；不得自动赋予新域 PerfectField。
- 任意同伦不变 PST 的最终陈述，若需要先取 Nis 层化，另须保留“层化后的 HI/转移结构”输入及其证明。不能把 NST 版本和一般 PST 版本混为一谈。

### 1.3 已完成但不代替主目标

已严格检查并直接审计：任意域的 H¹(A¹,F)=0；特征零所有权重的原 Milnor K 与原 H^{q,q} 双向比较；任意域的原普通 Nis 层复形 Z(1)→Gm[-1] 拟同构及任意光滑 X 上的上同调推论。后两项不提供一般高次 strict A1，不再扩大到特征 p 或带转移导出范畴的额外目标。

---
## 2. 冻结基线：哪些能直接使用，哪些仍是合同

“已验证”指当前源码字节有匹配的严格成功记录；重要终点还有直接消费者与标准公理检查。本次只重核关键终点，不宣称重建整个工程。仅带假设的中间定理，不按名称升级为无条件生产器。

### 2.1 已闭合的几何与局部输入

- `h_one_affineLine_eq_zero`：任意域、HI Nis 带转移层，原 ordinary H¹(A¹,F) 消失。没有预设修正对应、截面或 pencil。
- `fieldZeroSectionPurity`：域上的原收缩商与原 Laurent 开集对的 relative H¹ 同构，映射就是原 signed boundary。它只覆盖域基底，不是任意维数零截面的纯性。
- `exists_zeroNeighborhood_local_lifting`：对光滑仿射基底 Spec R、含整个零截面的仿射 Zariski 开集 V，围绕给定基点选一次 D(r)；每个原 F(V∩Gm) 截面限制后是 whole Gm_D(r) 截面与 V_D(r) 截面的差。没有提供 frames、截面、家族有限平坦等前提。
- `boundaryEtaleExcisionIso`：真实小 Nis 站点的边界层 étale 切除，保留原 closed inverse image、余核及代表元。它不是全局截面余核满射。
- `exists_smooth_cartier_etale_cylinder_comparison_over_base`：从原光滑 Cartier 对和一点产生共同 étale 邻域，保留原限制闭子概形、实际圆柱、基域映射以及 separated/QC 性质。没有 caller-supplied chart。
- `sectionQuotientRestriction_mono`：真实 Nis 方块上的原截面余核限制是单射；邻域中可延拓的原截面可由真实粘合回去。它只解决关系反射，不解决代表元满射。

### 2.2 已闭合的上同调桥

- 原所有点 Nis germ 的乘积已构造为真正带转移层；signed 作用、选择无关性、复合、graph、identity、层性质、原 F 的单射以及 transfer-injective 的 retract 都已证明。
- 原 germ 与剩余域小站点真实 inverse image 的同构、代表元公式和 étale graph 自然性已证明。原点不要求闭，也不要求剩余域映射是同构。
- 任意有限型 étale field-site 对象的真实剩余域分解及普通层 evaluation 正合性已证明；对任意 Spec K→X 的 direct image，已得到逐截面满射及正合性。
- `cohomologyAtBaseEquiv` 已证明原 big SmoothSite ordinary H 与原 small-site ordinary H 的比较。真正构造了正合左伴随和正合限制，没有假定限制保持内射对象。
- 特殊乘积短正合引理、具体 injective-step 的 ordinary Ext 维数移位判据已证明；判据所需的整族实际步骤还未完全构造。

### 2.3 仍不得按“完成”使用的接口

- `contractionToBoundary` 目前是正确的指定映射，不是一般基底的 IsIso。
- `exists_dataOfBoundaryFrames` 真能生成截面、零概形与端点，但仍显式输入好曲线、紧化、完整边界和 frames。
- 当前有限投影 producer 真能在指定点保持微分秩，并使原非约化闭集有限；尚未给整个相关纤维的坏集控制或完整 standard triple。
- germ envelope 的普通高次无同调性、普通 Hq 的转移结构、henselian 连续性、两个 Leray consumer 和最终双归纳均未结束。

---
## 3. 主依赖图：以验收关口而非文件数量推进

$G_0 → G_1 → G_2 → G_3 → P_1$

G0：固定原 étale 图与扩大坏集；G1：一次 target good presentation；G2：有限正规化提升 source；G3：完整 frame/同一缩基/原图比较；P1：原 punctured 截面的局部差分提升。

$P_1 + Z_0 + R_0 → P_2 → P_3$

Z0 是已证 Zariski 零邻域提升；R0 是关系反射及必要的单射桥；P2 是原 canonical contraction→真实 Nis boundary 的局部双射；P3 是保留乘积自然性的余维一纯性。

$T_0 → T_1 → T_2 → T_3$

T0 是已证 all-point envelope 与 field-site 接口；T1 是实际自然乘积层同构；T2 是具体 ordinary acyclicity；T3 是原 ordinary Hq 的转移及自然性。

$C_0 + C_1 + C_2 + P_3 + T_3 → L_1 → H_1 → H_2$

C0：真实连续性；C1：域上全部 A1 开集的消失；C2：非层 Hq 系数的收缩/边界控制；L1：有限阶 Leray 边缘引理；H1：henselian 维数归纳；H2：全局次数归纳并识别原投影映射。

合并纪律：每条箭头须有实际 map 或自然同构。任何包都不得把后继结论作为 typeclass、existence field、vanishing premise 或所谓“标准兼容性”反向输入。

---
## 4. 几何主线的重构：只做一次 target presentation

### 4.1 为什么不继续两边独立选投影

两个 Noether normalization 或两个 smooth chart 的存在性，不产生同一曲线基底，也不产生原 étale 态射在紧化之间的有限延拓。当前大量正确的同坐标消元结果可复用，但其终点合同仍比实际 consumer 弱。

推荐先固定原 separated quasi-finite étale 态射 f:Y→X。取真实有限正规化包络，使原 Y 是开子概形；把遗漏边界的有限像 B 纳入目标坏集。证明这个像是适当闭集，并逐分支去掉无关部分。随后只对目标对 (X,Z∪B) 构造好三元组，再在目标紧化的同一函数域图中提升源紧化。

该拆分由 [R2] 的 4.2、4.12 给出兼容紧化的明确依据；本项目只使用其经过核对的几何步骤，不整体沿用该旧文中已知有误的后续命题。

### 4.2 G1 的真实输出合同

输入应是原目标 X、适当闭集 T=Z∪B、允许开集及有限指定点。第一阶段允许无限完美基域。

输出必须包含：原 X 的一个真实开邻域 X′；新光滑仿射曲线基底 S；normal proper 相对曲线 C/S；X′→C 的开嵌入；X′→S 的相对维数一光滑性；完整 infinity 和需要保留的闭集在 S 上有限、互不相交且位于共同仿射邻域。源与目标原开集的 restriction equations 必须输出。

最低充分条件不必是最强 Bertini：若能证明指定 S-纤维内整个坏边界为零维、指定点仍保留且 Z 不碰删去部分，再经 proper/准有限的真实缩基即可。但“只在指定点光滑”严格不够。不得把整条纤维条件放回输入而称 producer 完成。

### 4.3 G2 的同基提升合同

输入 G1 的 target triple 和原 f。必须证明 f 的非有限位置落在已扩大的支持中，且原需要保留的 Z 的逆像仍有限并与原同构数据一致。由目标紧化在原源函数域中的正规化，构造实际有限紧化态射。

然后逐项推出：原源的开嵌入；完整源边界的像受目标 infinity∪T 控制；有限映射的共同仿射逆像；保留源对 S 光滑（由 étale f 合成得到）。这些步骤比再给源选一个新投影更窄，也避免无意义的两套坐标匹配。

### 4.4 G3 与现有 pencil 的对接

消去 graph ideal frame 和全部 twist frame 的输入：在完整有限边界上选同一个原基底邻域 D(r)，将 O(1) 的一个 frame 传递到所有正幂和两源；所需相等在整个原非约化边界上证明。

canonical graph ideal 的 restriction/pullback 同构必须保留原 inclusion。任何紧化可以在边界处奇异；光滑性只施加在实际 retained 曲线。Serre 使用已经构造的有限 C→P^N，而不是一个没有提供的 projective embedding。

最后消费已证 relative-curve producer，得到原截面的限制差分，而不是要求所有缩小后新截面的全局满射。用固定符号：

$A_0=s_Δ·b·d, \quad A_1=a·n, \quad α=Z(\text{pencil})-Z(bd)$

$λ=Z(a)-Z(b), \quad ψ=Z(d)-Z(n), \quad α_0=\mathrm{graph},\quad α_1=λ-ψ$

本报告中的这些式子规定验收符号；实现必须保持原 Cor 的实际 source/target 图与所有长度重数。

---
## 5. 为什么现有有限投影仍不足：可执行反例测试

### 5.1 同时有限、指定点 étale，仍有整条坏纤维

取 k=Q，X=A²_{s,t}，新曲线基底坐标 p=s²t，ambient 坐标 v=s+t。映射 (s,t)↦(v,p) 有限，因为原 s 满足

$s³-vs²+p=0, \qquad t=v-s.$

在 x=(1,0) 的 Jacobian 行列式为 1，因而 ambient map 在 x étale。闭集 Z=V(s−1) 沿 p 映到 A¹ 为同构，所以整个指定 Z 也有限。

然而 dp=2st ds+s²dt 在整条 V(s) 上为零；该一维分支都位于 p=0。删掉非光滑部分会制造一整条特殊纤维的边界，保持 p(x)=0 的缩基不能使它有限。

这个反例不否定好表示存在；它否定“当前输出条件已经足够”的推理。新的 G1 消费者应有回归测试，不能错误接受这组数据。

### 5.2 其他必须保留的失败检查

- D(1+s t) 含零截面，但不能在保持 s=0 的原基底邻域任意换成 monic 主开细化。现有任意仿射 Zariski 提升无需倒退到此假设。
- 选中零点的平方根 1+t étale 邻域，一般没有任何含零的 Zariski section。故 Zariski 开邻域不是 Nis 邻域的余终子系。
- 对原 A¹_S 投影直接做有限正规化，missing boundary 可含整条特殊 P¹。即使删掉显然无关的连通分支，带 degree drop 的例子仍可能在无穷远出现 base point；不能宣称原投影必有好有限紧化。
- 先选有限 θ，再把 θ 的临界集并入 I 并重新投影，会改变临界集。若 θ 已把指定点和另一个坏点合并，后续只用 θ 的坐标不可能再分开。

### 5.3 优化路线的停止条件

当前同坐标消元可以作为 G1 的实现工具。但只有在同一次选择中证明了纤维分离及完整坏集控制，才能替代原典的一般投影。若剩余论证反复引入“重新把新坏集加进去”，即触发停止条件：保留已有代数成果，转向一次固定 incidence/投影参数空间的避免定理，而不是无限追加同类局部引理。

---
## 6. 从局部差分到真正的边界纯性

### 6.1 P1：最小需要的局部提升，不先做全部 22.2

对原 Nis 方块及其 punctured-source 截面 τ，构造允许的目标/源开缩小与真实截面 a,c，使 τ 的原 restriction 等于 a 的拉回与 c 的限制之差。优先只实现 [R2] 4.12(2) 这一强度，再接已经完成的 Zariski 零邻域提升。

不能把结论强化成“缩小后每个新截面在原开集上都提升”；这种量词变化会制造不必要或错误的目标。也不能仅给一个存在的抽象群同构。

### 6.2 P2：原指定映射的两侧分别验收

目标对象保持当前 true small-Nis inverse image 的 boundaryCokernel。通过真实 Lan 代表元、sheafification 的局部代表及局部相等关系，把 P1 变成 `contractionToBoundary` 的局部满射。

单射另设关口：用已经证明的 Nis 方块余核关系反射，结合零邻域比较的关系侧；必要时补 [R2] 4.12(1) 强度。原 `toContraction_contractionToBoundaryPresheaf` 只是交换公式，不是已经存在的左逆。若改用域检测，必须先证明实际 kernel 有所需 PST/HI 结构。

验收必须是这个 canonical map 的 IsIso，并检查原 Laurent 代表元、signed boundary、系数态射和基变换。只构造一个别的同构不算完成。

### 6.3 P3：一般余维一与乘积相容

直接复用已证的原 smooth Cartier pair 共同 étale 圆柱邻域和真实 boundary-sheaf étale excision；两次运输得到局部余维一比较。对 X×T、Z×T 的同一选择及 T=A¹，需保留相应自然性。

还须有实际左端单射 F→j_*j*F，才有供高次使用的短正合列。不能从定义余核直接推出单射；应消费真实 dense-open injectivity 及其适用假设。

### 6.4 重要强度关口：P=Hq 不是层

高次阶段的 P=H^q_Nis(-,F) 通常是预层且其层化为零。这不允许把 `a(j_*j*P)` 换成 `j_*j*(aP)`；前者正承载需要控制的边界信息。

必须选择并正式完成一条路线：

A. 通用 HI PST 版本的边界比较及 contraction/sheafification 交换，按 MVW 22.2、23.5 的正确依赖实现。

B. 为 P=Hq 保留真实预层边界，并用所有相关域上的 A¹ 开集（特别 Gm）消失，再加适用的域检测，证明其收缩层化为零。这可能绕过整个 22.2，但仍要实际证明域检测、换基/连续性和该特殊预层版本。

建议先按 B 制定精确合同，并设置“是否足够消费高次 R^qj_*”测试；若需要重新证明接近完整 22.2 的内容，则回归 A，不在两条半成路线间来回切换。

---
## 7. 普通上同调转移：保留当前工程最短链

### 7.1 T1：把对象级比较升级为实际自然层同构

固定 X，记 i_x:Spec κ(x)→X。需要证明已有 envelope 在小站点上的限制，真正自然同构于

$E(F)|_X ≅ ∏_{x∈X} i_{x*}i_x^*(F|_X).$

对每个 étale V→X，先用实际纤维分解得到各 κ(u) 分量，再重排嵌套乘积。组件箭头必须是原 residueFieldMap；对 V 的限制自然性与原 section-unit 的对应都须检验。已有 objectwise germ iso 和图自然性可用，但完整 product gluing 仍是一条独立终点。

### 7.2 T2：只对这个特殊乘积证明无同调

对每族 field-site 层 A_x，选择真实普通内射嵌入 A_x→I_x，令 Q_x 为真实余核。先明确实际宇宙中的 EnoughInjectives 实例。

因为 inverse image 正合，i_{x*}I_x 内射；内射的实际乘积也是内射。field-site direct image 已证明逐截面满射，因此这里的乘积短正合成立。使用 Ab/预层中的乘积正合性，不推断任意层范畴满足 AB4*。

由原 sections representability 得到每一步 Hom 满射，再直接调用已验证的 `ext_eq_zero_of_resolution_steps`。只需构造足够执行有限次维数移位的具体步骤，不必新增完整 resolution 框架。

### 7.3 T3：原 ordinary Hq，而不是替代上同调

T1、T2 加已经完成的 big/small Ext 比较，给原 envelope ordinary-acyclic。transfer-injective F 是它的已证 retract，因此 F 的底层 ordinary H 在正次数消失；不声称底层 ordinary sheaf 本身内射。

设 Ztr_Nis(X) 为原 representableLarge 的 transfer sheafification，构造原普通 free source 到其底层的真实 map η_X。比较公式为

$c_n(e)=η_X^*(\mathrm{mapExactFunctor}(e)).$

degree 0 是真实 sections equivalence。沿 transfer-injective 嵌入和余核，用上述 ordinary acyclicity 与两边原 Ext 正合列归纳证明 c_n 双射。最后证明 X 与系数的自然性，通过 c_n 将 Cor 作用传到原 ordinary Hq；graph 限制必须等于原 pullback。

工程选择：理论上可用一整个 dependent family 类别的 exact adjunction 一步处理，但现阶段缺其 Abelian/Ext 接口。已有具体步骤维数移位更短，禁止为此重开通用范畴基础工程。

---
## 8. 不能漏掉的连续性、域基例与高次工具

### 8.1 C0：真正的局部对象

Sm/k 的有限型对象不包括任意 henselization。当前针对“本身已 smooth 的 henselian 谱”的定理，不是 MVW 高次归纳需要的全部情形。

应分别证明：原 section 的 filtered colimit；ordinary H 的有限阶段下降和连续性；higher direct image 的 stalk 与局部 cylinder cohomology 的识别。不能用一次 germ-level 比较冒充所有 derived continuity。

接口类别应对局部化、henselization、取正则参数商封闭，并明确它们如何由光滑有限型 k-模型出现。只知道正则局部 k-代数在完美域上几何正则，还需实际进入现有 site/cohomology 的比较。

### 8.2 C1：域上基例的真实强度

已有 H¹(A¹,F)=0 不等于域上所有 A¹ 开集、所有正次数都消失。下一合同应覆盖原 field extension 上的 HI 系数、A¹ 的所有相关开集；高于一次的部分需真正的曲线 Nis cohomological-dimension ≤1 或等价有限阶证明。

不要把 function field K 当 Sm/k 对象，也不要把 K 默认为完美。换基后的 F_K、其转移与 HI、原评价群之间都需要真实定义/连续性。

### 8.3 L1：只实现需要的 Leray 边缘结果

对开放嵌入 j，只需：当 0<q<n 的 R^qj_* 消失，原 edge map 在次数 n 单射。不得额外要求 R^nj_*=0。

对投影 π，需要当 0<q≤n 的 higher direct image 消失时，在次数 n 得到同构，并将其识别为原 π 拉回。可用实际 injective complex 与截断/锥构造证明这些 consumer；不必先搭完整通用谱序列。

以上只是选择较小实现范围，不是省掉 derived functor、stalk 识别或边缘映射自然性。若采用替代 Čech 路线，同样必须比较到原 Ext。

---
## 9. 最终双归纳如何真正结束

外层归纳必须对“所有 HI Nis 带转移层 F”同时进行，而不是只固定一个 F；否则无法在下一步把归纳假设用于 F_-1。

### 9.1 24.3 型限制单射：拆成两个 map

$Hⁿ(S×A¹,F) → Hⁿ(S×A¹,j_*j*F) → Hⁿ(U×A¹,F).$

第二个 map：由非层 P=Hq 的边界/收缩控制获得低次数 R^qj_* 消失，再用 L1 的单射结论。

第一个 map：由真实短正合列与余维一边界比较。n>1 时，相关 H^{n-1}(Z×A¹,F_-1) 用低次数 HI 归纳化为 henselian Z 上的高次消失。n=1 时这是 H⁰，不能称其为零；必须先在 S 上利用 Γ exactness 得 section 满射，再用 F 与 F_-1 的 HI 和 ×A¹ 自然性搬运。

### 9.2 Henselian 局部维数归纳

维数零是正确换基解释后的域基例。正维时，在任意真开集上用较小局部维数归纳和零截面，证明 cylinder cohomology 的 restriction 为零。再取 r∈m\m² 的正则参数，借上段证明该 restriction 单射，两者合起来得源为零。

这里 regular quotient 的形式光滑/几何正则性、Hensel 性及连续性必须是真正已经实例化的事实。它们不是一句“取局部坐标”就自动拥有。

### 9.3 回到全局原投影

所有真实 Nis stalk 上消失给 R^nπ_*F=0；配合低次数归纳和 π_*F≅F 的实际 HI map，用 L1 的投影 consumer 得最终 ordinary Hⁿ 同伦不变性。最后检查结果落在原 `IsStrictA1Invariant`，不增加 purity、presentation 或 vanishing 类型类。

禁止倒用：strict 之后的半局部消失、高余维纯性、Gersten 分辨或已经依赖 strict 的同伦纯性。尤其不能用 ordinary injective 的余核“仍然 HI”作次数归纳。

---
## 10. 执行路线：先冻结合同，再并行合并

### 波次 I：现在就能并行的四个有界包

G-A：单 target good presentation。输入真实扩大坏集与指定闭点；输出整条相关纤维的好曲线条件。优先无限完美域版本。负责人不得仅交 selected-point Jacobian，必须通过第5节的反例测试。

G-B：有限正规化 source lifting 与 frame join。以固定 target-triple 合同为输入，输出原 f 的同基有限延拓、完整源边界和实际 frames。与 G-A 并行，但最终必须消费其真实 producer，不永久保留目标级假设。

T-A：自然 product sheaf iso、具体 injective 步骤及 ordinary Ext 消失。保持所有点，不退回 closed-point 包络；完成后接 ordinary Hq 转移。

C-A：高次连续性与有限阶 Leray 的依赖审计，先选择原定义下最小所需 theorem。可以先做不依赖几何的有限阶范畴引理，但不得先给更强通用框架建大量未消费模块。

### 波次 II：只在输入终点通过后开始

P-A：P1 的原截面局部差分提升；canonical boundary 的局部满射与单射，至少有一个真实任意 Nis 代表元的 end-to-end test。

P-B：一般 HI PST 边界及特殊 P=Hq 的收缩消失合同；与已有 étale pair geometry 合成乘积自然的余维一比较。

F-A：有限域的两个互素次数下降，包含有限阶段 spread-out、同一原开邻域、Cor 转移与限制交换及整系数 Bézout。未完成前维持无限域标签。

### 波次 III：最终集成

分别验收 n=0、n=1、n>1、henselian dim=0、dim>0、有限完美域六个分支。最后给原 π 拉回的 IsIso、自然性、以及整个依赖闭包标准公理审计。

### 每个工作包必须交付的五件事

1. 可直接写成 Lean theorem 的精确输入、输出及原 map。
2. 本包真正消去的假设；未消去的几何/范畴条件明确列出。
3. 一个实际消费者，而非重复 theorem 类型的薄包装。
4. 当前源码 SHA 匹配的成功严格日志与标准公理审计。
5. 与下一包接口的一次真实实例化。仅源码存在、仅条件式模板或仅一侧同构均不算该关口完成。

### 合并纪律与改路触发器

- 禁止用文件数或已编译行数表示完成比例；以 G/P/T/C/L/H 关口消失为进度。
- 几何若不断重新选择投影而无法控制旧坏集的像，回到一次参数空间避免定理；不无限追加补丁。
- 非层 Hq 的边界若必须先假设完整 22.2，则明确切换后备路线，不把该依赖隐藏。
- 实例/宇宙问题若能由现有 Grothendieck/EnoughInjectives 接口解决，优先小实例化；若必须建立新范畴，先重新比较具体步骤路线的成本。
- 不提高心跳、递归或资源上限来替代证明分解；不加入新公理、sorry 或未验证的 compatibility fields。

---
## 11. 首批重新启动的精确顺序

本报告交付后，先并行 G-A、G-B、T-A，另保留一个容量给 C-A 的独立连续性/有限阶 Leray 审查。优先完成 T-A 这个现有接口已充分、风险较低的闭环，同时让 G-A 处理最高风险的 whole-fibre 控制。

G-A 不再泛称“完成 simultaneous Bertini”。首个验收是目标端扩大坏集的一次好表示，或一个确实足够且通过反例检查的更弱 whole-fibre avoidance。G-B 则先形式化 [R2] 4.2 的原有限正规化 lifting，避免再次给源独立选坐标。

在 P1 真正完成前，不并行启动最终 higher strict theorem 的巨型组装。可提前建立其精确接口与小边缘引理，但任何总定理必须最终消去这些前提。

不提供未经根据的工期承诺。风险排序：G-A 与 C0 高；非层系数 P-B 高；T-A 中等且接口较成熟；已有 frame/pencil 消费与最终纯 map 运输相对低，但仍需真实核验。

---
## 12. 关键源码与检查索引

以下是读核边界，不是全工程构建声明。路径相对于项目根目录；SHA 前缀仅供定位，完整值与匹配日志保存在源包证据中。

- Cohomology/SheafCohomologyH1AffineLineVanishing.lean：bfcc16b92122；原 H¹ 终点。
- Cohomology/A1/ZeroNeighborhoodLocalLifting.lean：578eadf57096；真实 Zariski 原截面提升。
- Cohomology/A1/ContractionBoundarySheaf.lean：fa5c5592a1cd；canonical map，不是 IsIso。
- Cohomology/A1/BoundaryEtaleExcision.lean：499bb6b4481b；真实边界层切除。
- Aglib/AlgebraicGeometry/SmoothCartierEtaleComparisonOverBase.lean：ad5e59bc29cd；原 pair 的 over-base 几何。
- Aglib/RingTheory/Etale/FiniteBadLocusProjection.lean：2e488cee3b64；局部微分＋有限坐标，不含 whole-fibre 合同。
- Cohomology/A1/RelativeCurveLocalLifting.lean：0f26a311d9c8；仍有原几何与 frames 的条件式消费者。
- Transfers/OriginalGermTupleEnvelope.lean：922698c683cd；真实转移层包络与 retract，不含 ordinary acyclicity。
- AlgebraicGeometry/Sites/FiniteEtaleCohomologyComparison.lean：7f0ca0f51038；原 big/small ordinary Ext 比较。
- Cohomology/SheafProductShortExact.lean：f349720c8206；仅消费明确的逐截面 epi，不断言所有层乘积正合。
- Cohomology/ExtAcyclicResolutionSteps.lean：2bbb6c8b1e36；具体 resolution-step 判据，实际 residue-family 步骤仍须构造。

已验证与未验证的分界以 theorem 参数为准。对 source-only PASS 而尚无独立直接审计的局部 frame 新引理，在合并前补直接消费者；不据此否定已完成模块，也不把它计作已结束的总关口。

---
## 13. 原典与版本说明

[R1] Mazza–Voevodsky–Weibel, Lecture Notes on Motivic Cohomology，Clay Mathematics Monographs 2，2006。
https://www.claymath.org/library/monographs/cmim02.pdf
定位按印刷页而非 PDF viewer 页序：11.17–18（86–88）；12.2、12.10（89、92）；13.3–4（99–100）；21.11（181–182）；22.2（陈述183、证明189–190）；22.7–8（184）；23.5–12（192–194）；24.1–4（197–199）。

[R2] Voevodsky, Cohomological theory of presheaves with transfers，核验标题和正文的原稿。
https://www.math.ias.edu/~dgrayson/Voevodsky-old-files/files/files-original/Dropbox/Published_papers/Motives/Collection/s3.pdf
只用经过逐项核对的 4.2（21–22）、4.12（29–30）来展开有限正规化与局部原截面提升。它补足 [R1] 的兼容三元组简写，不用来跳过 [R1] 明示的有限域步骤。

[R3] MVW 官方勘误。
https://sites.math.rutgers.edu/~weibel/Books/MVW.errors.pdf
Exercise 12.10 的包络必须取所有点，不能只取闭点。已构造的原 all-point envelope 与此一致。

[R4] IAS Voevodsky 书目与勘误说明。
https://www.math.ias.edu/Voevodsky/voevodsky-publications_abstracts.html
旧 CohTh 4.23 的论证有错误；采用 [R1] 22.10 的修正，保留进一步缩小和原截面 restriction 的量词。不要把旧文的一条全局满射当作本项目捷径。

本文件中的工作包合同、反例计算、代码强度划分和实现取舍，是针对当前项目的研究审计；并非将原典中的省略步骤当作已经形式化的事实。原典引用负责定位数学路线，实际完成状态由当前源码和直接检查证据负责。


---

# 补遗草案：绕开22.2时，高次非层系数真正需要什么

2026-10-17 13:26 UTC 补充：经两次独立原典审查后纳入；以下为待实现证明路线，不是已编译结论。

## 决策结论

对当前最终目标“已经是 HI Nis 带转移层 F 的 strict A¹”，可以完全不把 MVW22.2、22.3、23.5列为前置。代价不是没有替代证明，而是明确加入以下两个弱化引理：

(EPI-P) 对任意 HI 带转移预层 P，canonical map
    (P₋₁)_Nis|S → B_P(A¹_S,0_S)
是层满射。对一般 P 不必证明单射/同构。

(ZERO-q) 若 q>0，P=H^q_Nis(-,F) 已由低次数归纳成为 HI PST，则
    (P₋₁)_Nis=0。

于是 EPI-P 立即给 B_P=0；23.11型真实 étale excision和smooth Cartier cylinder charts将其传递到一般smooth divisor；23.8型比较给 R^qj_*F=0。这恰好是24.3右侧Leray edge injection所需。

对已经是层的 F，仍需原 canonical contractionToBoundary 的完整 IsIso，并保留与乘积 T=A¹ 的自然性；它负责24.3左侧 short exact sequence，不能只用EPI-P代替。

如果只完成 F 为层的23.10，而未加入EPI-P或另一项真的非层边界比较，B路线尚未闭合，缺口恰在 q>0 时 R^qj_*F 的消失，第一次在 n=2、q=1出现。n=1的成功不会自动填上它。

## 非层边界的正确对象，不能先把P层化

对 j:V=X\Z→X，先在实际small étale/Nis neighborhoods W→X上定义原预层
    Q_P(W)=coker(P(W)→P(W×_X V))。
然后定义
    B_P(X,Z)=i^{-1}a_Nis(Q_P)。

该次序不可改变。对 P=H^q(-,F), q>0，虽然a_Nis(P)=0，a_Nis(W↦P(W×_X V))一般正是非零的 R^qj_*F。把P先换成0再取开放直像，会把需要证明消失的对象按定义删除，属于错误短路。

真实23.8桥是：在普通上同调/大小站点比较与连续性已经建立后，
    i_*B_{H^qF}(X,Z) ≅ R^qj_*F  (q>0)。
其证明只用高次上同调预层局部为零、层化正合、R^qj_*的局部上同调描述，以及支持于Z的层的closed recollement；不需要 strict A¹、22.2或23.5。

现代码 BoundaryCokernelSheaf.lean 和 ContractionBoundarySheaf.lean 的参数是已经为层的 F。一般P版本不能仅复用其类型而传入P_Nis。EPI-P须以以上原Q_P定义另行接上现有true inverse image。CohTh4.12(2)+任意affine Zar零邻域提升在原P截面上成立，正好能证明EPI-P，不需要一般P的关系反射单射。

## ZERO-q的首选短证明：11.2＋22.4，不要求完整22.7开集版

固定 q>0、F为HI NST，并假设普通 P=H^q(-,F) 已有真实转移和HI。

1. Field continuity：对每个smooth integral k-model的函数域 E，
   P(E)=H^q_Nis(Spec E,F_E)=0。
   这里第一个等号是原ordinary H的连续性/field coefficient comparison，不能把“field站点无高次”直接当成filtered colimit等号。第二个等号由field Nis global sections正合，独立于strict A¹。

2. 用11.1→11.2的generic detection：若HI PST G在所有这类函数域上为0，则a_Zar(G)=0。应用于P，得a_Zar(P)=0。

3. 对任意所需函数域 E，将P沿separable extension k⊂E按2.10延拓。MVW22.4说：任意HI PST在A¹_E的Zariski开集上本来就是Zariski层。这一步来自field curve的标准三元组split MV，独立于22.2，且不要求P本身是全局层。因此
   P(Gm_E)=(a_Zar P_E)(Gm_E)=0。
   a_Zar P_E=0优先从a_Zar P=0直接spread out：P_E(V)的每个截面来自某个smooth k-model Vα；在Vα上用使其为零的Zariski覆盖，拉回到V即成为零覆盖。这样无需在可能不perfect的E上再次调用受限版本11.2。所有有限型覆盖/截面的下降与filtered-colimit兼容须实际证明。

4. 原P₋₁(E)=coker(P(A¹_E)→P(Gm_E))=0。P₋₁本身仍是HI PST；再用11.2得a_Zar(P₋₁)=0，因Nis拓扑更细，a_Nis(P₋₁)=0。到此完成ZERO-q，不曾用23.5。

若实现更顺手，可改用“22.7全部开集版＋11.2”：22.7给H^q(Gm_E,F_E)=0，直接从步骤4接下去。两种证明选一即可，不必同时实现。

## 11.2、域范围与收缩：真实假设

11.2在印刷页83写“every field E over k”；证明实际只需要所有smooth integral有限型k-schemes的函数域，因为11.1将每个局部stalk嵌入generic value。故有限生成、separably generated的这类扩张足够；不要求所有任意巨大扩张，也不要求所有point residue fields。

关键区别：所需E是smooth模型的函数域，不是任意闭点的剩余域。它在任意k上都有separable/smooth-model性质。MVW2.10本身明确假设k⊂E separable。perfect k时这些有限生成E可分生成，但E自己在正特征下未必perfect。切勿把PerfectField E当作自动实例。

11.1/11.2的陈述不要求perfect或infinite。原证明11.17在infinite分支做geometry，finite分支借11.18和互素transfer下降。若本轮只实现infinite perfect k，则generic detection也只能按该已证分支使用；有限域最终版本仍需同一下降，不可略过。

P₋₁的transfers和HI完全直接继承：参数化P(-×A¹)、P(-×Gm)用exterior finite correspondences给PST，限制是PST morphism，取原objectwise cokernel；两个参数化预层均HI，故cokernel HI。不涉及层化或23.5。
源码已经有精确支撑：PresheavesWithTransfers/Contraction.lean定义真实PST收缩；ContractionInvariance.lean的contraction_isA1Invariant对任意P生效。ContractionSheaf.lean用unit-section kernel进一步证明已为HI NST的F的收缩仍是HI NST；也明确不声称一般P的sheafification-commutation。

## 22.7是否循环，以及当前最少需要它哪一部分

22.7并不依赖strict A¹：它用curve Nis cohomological dimension≤1消去n>1；n=1用Čech H¹、Nis cover的distinguished-square refinement、étale曲线在P¹上的有限光滑正规紧化，以及21.6在field curve上的split MV。没有22.2、23.5或24.x。

但已有 h_one_affineLine_eq_zero 只证明A¹，不自动证明Gm或任意开集。因此若选上面的22.7替代链，须实际补全部开集版，不能重命名现定理。

首选11.2＋22.4链避免这个新要求。24.2的d=0只需A¹_E的所有高次消失：已有任意域H¹(A¹)=0，加small Nis curve cohomological dimension≤1及big/small比较即可；无需为了此basecase额外证明所有A¹开集。

## 从弱化边界到24.3：最短闭合链

全局按次数n归纳，归纳命题必须同时量化所有HI NST系数，不是只固定一个F。

A. 低次数归纳＋原ordinary H的转移：对0<q<n，P_q=H^q(-,F)是HI PST。
B. ZERO-q＋EPI-P＋一般smooth Cartier étale模型：B_{P_q}(S×A¹,Z×A¹)=0。
C. 真实23.8：R^qj_*F=0，0<q<n。有限阶Leray edge lemma给24.3右箭头η单射。
D. 22.8只用于已经是Nis层的F；此时F本来是Zar层，F_Zar=F，故generic/dense restriction injection直接给F→j_*j^*F单射。这里无须22.2。
E. 层系数F的canonical纯性同构及乘积自然性给实际短正合列
   0→F→j_*j^*F→i_*F₋₁→0。
F. n>1时，F₋₁是HI NST（直接kernel论证），对“所有系数”的n−1归纳给
   H^{n−1}(Z×A¹,F₋₁)=H^{n−1}(Z,F₋₁)=0，后一个等号由henselian local Nis Γ正合。
G. n=1时，先在原henselian S上对E的短正合列取Γ，得F(U)→F₋₁(Z)满射；再用F、F₋₁的ordinary HI及纯性map对×A¹的自然性，取得cylinder上的满射。不能把一般local scheme上的Γ默认当正合。
H. E的long exact sequence给24.3左箭头τ单射；与C组合得到原restriction单射。
I. 24.2的维数归纳：proper open U上的restriction在cohomology中为零，而H保证其单射；field basecase使用上述A¹消失。最后π的有限阶Leray比较恢复全局实际projection同构。

因此替代链在数学上闭合，但真实待验收内容是EPI-P、ZERO-q中generic detection/field continuity、23.8 ordinary comparison，以及层系数canonical纯性及product自然性。不得把这些压成一句“由已知23.10即可”。原路线图若保留C0/ordinary H transfer这些明确任务，加上本补遗的精确EPI-P与ZERO-q，就无需把完整22.2重新放回关键路径。


## 实现时须显式验证的四项相容性

1. 函数域取值与原普通上同调的连续性比较；或另行证明高次预层的 Nis 局部零经 generic 分裂覆盖给出 generic germ 为零。
2. 可分生成扩张 E/k 上 P_E 的 transfers、HI 和每个截面的实际 smooth k-model 下降。
3. 下降截面的有限 Zariski 零覆盖拉回后仍覆盖 V_E，才推出 a_Zar(P_E)=0，不假设层化和基变换无条件交换。
4. 原 (P₋₁)(E) 与 coker(P_E(A¹_E)→P_E(Gm_E)) 的 canonical 比较，须由 product-model 相容与 filtered colimit 正合证明。
