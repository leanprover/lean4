// Lean compiler output
// Module: Init.Lean.Meta.KAbstract
// Imports: Init.Lean.Data.Occurrences Init.Lean.HeadIndex Init.Lean.Meta.ExprDefEq
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_HeadIndex_HeadIndex_beq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___main(lean_object*);
uint8_t l_Lean_Occurrences_contains(lean_object*, lean_object*);
uint8_t l_coeDecidableEq(uint8_t);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Init_Lean_HeadIndex_1__headNumArgsAux___main(lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_804; uint8_t x_805; 
x_804 = l_Lean_Expr_hasLooseBVars(x_5);
x_805 = l_coeDecidableEq(x_804);
if (x_805 == 0)
{
lean_object* x_806; uint8_t x_807; 
x_806 = l_Lean_Expr_toHeadIndex___main(x_5);
x_807 = l_Lean_HeadIndex_HeadIndex_beq(x_806, x_3);
lean_dec(x_806);
if (x_807 == 0)
{
uint8_t x_808; 
x_808 = 0;
x_10 = x_808;
goto block_803;
}
else
{
lean_object* x_809; lean_object* x_810; uint8_t x_811; 
x_809 = lean_unsigned_to_nat(0u);
x_810 = l___private_Init_Lean_HeadIndex_1__headNumArgsAux___main(x_5, x_809);
x_811 = lean_nat_dec_eq(x_810, x_4);
lean_dec(x_810);
x_10 = x_811;
goto block_803;
}
}
else
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_812 = lean_ctor_get(x_5, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_5, 1);
lean_inc(x_813);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_814 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_812, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_814) == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_815 = lean_ctor_get(x_814, 0);
lean_inc(x_815);
x_816 = lean_ctor_get(x_814, 1);
lean_inc(x_816);
lean_dec(x_814);
x_817 = lean_ctor_get(x_815, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_815, 1);
lean_inc(x_818);
lean_dec(x_815);
x_819 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_813, x_6, x_818, x_8, x_816);
if (lean_obj_tag(x_819) == 0)
{
uint8_t x_820; 
x_820 = !lean_is_exclusive(x_819);
if (x_820 == 0)
{
lean_object* x_821; uint8_t x_822; 
x_821 = lean_ctor_get(x_819, 0);
x_822 = !lean_is_exclusive(x_821);
if (x_822 == 0)
{
lean_object* x_823; lean_object* x_824; 
x_823 = lean_ctor_get(x_821, 0);
x_824 = lean_expr_update_app(x_5, x_817, x_823);
lean_ctor_set(x_821, 0, x_824);
return x_819;
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_825 = lean_ctor_get(x_821, 0);
x_826 = lean_ctor_get(x_821, 1);
lean_inc(x_826);
lean_inc(x_825);
lean_dec(x_821);
x_827 = lean_expr_update_app(x_5, x_817, x_825);
x_828 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_828, 0, x_827);
lean_ctor_set(x_828, 1, x_826);
lean_ctor_set(x_819, 0, x_828);
return x_819;
}
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_829 = lean_ctor_get(x_819, 0);
x_830 = lean_ctor_get(x_819, 1);
lean_inc(x_830);
lean_inc(x_829);
lean_dec(x_819);
x_831 = lean_ctor_get(x_829, 0);
lean_inc(x_831);
x_832 = lean_ctor_get(x_829, 1);
lean_inc(x_832);
if (lean_is_exclusive(x_829)) {
 lean_ctor_release(x_829, 0);
 lean_ctor_release(x_829, 1);
 x_833 = x_829;
} else {
 lean_dec_ref(x_829);
 x_833 = lean_box(0);
}
x_834 = lean_expr_update_app(x_5, x_817, x_831);
if (lean_is_scalar(x_833)) {
 x_835 = lean_alloc_ctor(0, 2, 0);
} else {
 x_835 = x_833;
}
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_832);
x_836 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_836, 0, x_835);
lean_ctor_set(x_836, 1, x_830);
return x_836;
}
}
else
{
uint8_t x_837; 
lean_dec(x_817);
lean_dec(x_5);
x_837 = !lean_is_exclusive(x_819);
if (x_837 == 0)
{
return x_819;
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; 
x_838 = lean_ctor_get(x_819, 0);
x_839 = lean_ctor_get(x_819, 1);
lean_inc(x_839);
lean_inc(x_838);
lean_dec(x_819);
x_840 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_840, 0, x_838);
lean_ctor_set(x_840, 1, x_839);
return x_840;
}
}
}
else
{
uint8_t x_841; 
lean_dec(x_813);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_841 = !lean_is_exclusive(x_814);
if (x_841 == 0)
{
return x_814;
}
else
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; 
x_842 = lean_ctor_get(x_814, 0);
x_843 = lean_ctor_get(x_814, 1);
lean_inc(x_843);
lean_inc(x_842);
lean_dec(x_814);
x_844 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_844, 0, x_842);
lean_ctor_set(x_844, 1, x_843);
return x_844;
}
}
}
case 6:
{
lean_object* x_845; lean_object* x_846; uint64_t x_847; lean_object* x_848; 
x_845 = lean_ctor_get(x_5, 1);
lean_inc(x_845);
x_846 = lean_ctor_get(x_5, 2);
lean_inc(x_846);
x_847 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_848 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_845, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_848) == 0)
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; 
x_849 = lean_ctor_get(x_848, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_848, 1);
lean_inc(x_850);
lean_dec(x_848);
x_851 = lean_ctor_get(x_849, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_849, 1);
lean_inc(x_852);
lean_dec(x_849);
x_853 = lean_unsigned_to_nat(1u);
x_854 = lean_nat_add(x_6, x_853);
lean_dec(x_6);
x_855 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_846, x_854, x_852, x_8, x_850);
if (lean_obj_tag(x_855) == 0)
{
uint8_t x_856; 
x_856 = !lean_is_exclusive(x_855);
if (x_856 == 0)
{
lean_object* x_857; uint8_t x_858; 
x_857 = lean_ctor_get(x_855, 0);
x_858 = !lean_is_exclusive(x_857);
if (x_858 == 0)
{
lean_object* x_859; uint8_t x_860; lean_object* x_861; 
x_859 = lean_ctor_get(x_857, 0);
x_860 = (uint8_t)((x_847 << 24) >> 61);
x_861 = lean_expr_update_lambda(x_5, x_860, x_851, x_859);
lean_ctor_set(x_857, 0, x_861);
return x_855;
}
else
{
lean_object* x_862; lean_object* x_863; uint8_t x_864; lean_object* x_865; lean_object* x_866; 
x_862 = lean_ctor_get(x_857, 0);
x_863 = lean_ctor_get(x_857, 1);
lean_inc(x_863);
lean_inc(x_862);
lean_dec(x_857);
x_864 = (uint8_t)((x_847 << 24) >> 61);
x_865 = lean_expr_update_lambda(x_5, x_864, x_851, x_862);
x_866 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_866, 0, x_865);
lean_ctor_set(x_866, 1, x_863);
lean_ctor_set(x_855, 0, x_866);
return x_855;
}
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; uint8_t x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_867 = lean_ctor_get(x_855, 0);
x_868 = lean_ctor_get(x_855, 1);
lean_inc(x_868);
lean_inc(x_867);
lean_dec(x_855);
x_869 = lean_ctor_get(x_867, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_867, 1);
lean_inc(x_870);
if (lean_is_exclusive(x_867)) {
 lean_ctor_release(x_867, 0);
 lean_ctor_release(x_867, 1);
 x_871 = x_867;
} else {
 lean_dec_ref(x_867);
 x_871 = lean_box(0);
}
x_872 = (uint8_t)((x_847 << 24) >> 61);
x_873 = lean_expr_update_lambda(x_5, x_872, x_851, x_869);
if (lean_is_scalar(x_871)) {
 x_874 = lean_alloc_ctor(0, 2, 0);
} else {
 x_874 = x_871;
}
lean_ctor_set(x_874, 0, x_873);
lean_ctor_set(x_874, 1, x_870);
x_875 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_875, 0, x_874);
lean_ctor_set(x_875, 1, x_868);
return x_875;
}
}
else
{
uint8_t x_876; 
lean_dec(x_851);
lean_dec(x_5);
x_876 = !lean_is_exclusive(x_855);
if (x_876 == 0)
{
return x_855;
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_877 = lean_ctor_get(x_855, 0);
x_878 = lean_ctor_get(x_855, 1);
lean_inc(x_878);
lean_inc(x_877);
lean_dec(x_855);
x_879 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_879, 0, x_877);
lean_ctor_set(x_879, 1, x_878);
return x_879;
}
}
}
else
{
uint8_t x_880; 
lean_dec(x_846);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_880 = !lean_is_exclusive(x_848);
if (x_880 == 0)
{
return x_848;
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_881 = lean_ctor_get(x_848, 0);
x_882 = lean_ctor_get(x_848, 1);
lean_inc(x_882);
lean_inc(x_881);
lean_dec(x_848);
x_883 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_883, 0, x_881);
lean_ctor_set(x_883, 1, x_882);
return x_883;
}
}
}
case 7:
{
lean_object* x_884; lean_object* x_885; uint64_t x_886; lean_object* x_887; 
x_884 = lean_ctor_get(x_5, 1);
lean_inc(x_884);
x_885 = lean_ctor_get(x_5, 2);
lean_inc(x_885);
x_886 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_887 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_884, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_887) == 0)
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_888 = lean_ctor_get(x_887, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_887, 1);
lean_inc(x_889);
lean_dec(x_887);
x_890 = lean_ctor_get(x_888, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_888, 1);
lean_inc(x_891);
lean_dec(x_888);
x_892 = lean_unsigned_to_nat(1u);
x_893 = lean_nat_add(x_6, x_892);
lean_dec(x_6);
x_894 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_885, x_893, x_891, x_8, x_889);
if (lean_obj_tag(x_894) == 0)
{
uint8_t x_895; 
x_895 = !lean_is_exclusive(x_894);
if (x_895 == 0)
{
lean_object* x_896; uint8_t x_897; 
x_896 = lean_ctor_get(x_894, 0);
x_897 = !lean_is_exclusive(x_896);
if (x_897 == 0)
{
lean_object* x_898; uint8_t x_899; lean_object* x_900; 
x_898 = lean_ctor_get(x_896, 0);
x_899 = (uint8_t)((x_886 << 24) >> 61);
x_900 = lean_expr_update_forall(x_5, x_899, x_890, x_898);
lean_ctor_set(x_896, 0, x_900);
return x_894;
}
else
{
lean_object* x_901; lean_object* x_902; uint8_t x_903; lean_object* x_904; lean_object* x_905; 
x_901 = lean_ctor_get(x_896, 0);
x_902 = lean_ctor_get(x_896, 1);
lean_inc(x_902);
lean_inc(x_901);
lean_dec(x_896);
x_903 = (uint8_t)((x_886 << 24) >> 61);
x_904 = lean_expr_update_forall(x_5, x_903, x_890, x_901);
x_905 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_905, 0, x_904);
lean_ctor_set(x_905, 1, x_902);
lean_ctor_set(x_894, 0, x_905);
return x_894;
}
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; uint8_t x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; 
x_906 = lean_ctor_get(x_894, 0);
x_907 = lean_ctor_get(x_894, 1);
lean_inc(x_907);
lean_inc(x_906);
lean_dec(x_894);
x_908 = lean_ctor_get(x_906, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_906, 1);
lean_inc(x_909);
if (lean_is_exclusive(x_906)) {
 lean_ctor_release(x_906, 0);
 lean_ctor_release(x_906, 1);
 x_910 = x_906;
} else {
 lean_dec_ref(x_906);
 x_910 = lean_box(0);
}
x_911 = (uint8_t)((x_886 << 24) >> 61);
x_912 = lean_expr_update_forall(x_5, x_911, x_890, x_908);
if (lean_is_scalar(x_910)) {
 x_913 = lean_alloc_ctor(0, 2, 0);
} else {
 x_913 = x_910;
}
lean_ctor_set(x_913, 0, x_912);
lean_ctor_set(x_913, 1, x_909);
x_914 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_914, 0, x_913);
lean_ctor_set(x_914, 1, x_907);
return x_914;
}
}
else
{
uint8_t x_915; 
lean_dec(x_890);
lean_dec(x_5);
x_915 = !lean_is_exclusive(x_894);
if (x_915 == 0)
{
return x_894;
}
else
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_916 = lean_ctor_get(x_894, 0);
x_917 = lean_ctor_get(x_894, 1);
lean_inc(x_917);
lean_inc(x_916);
lean_dec(x_894);
x_918 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_918, 0, x_916);
lean_ctor_set(x_918, 1, x_917);
return x_918;
}
}
}
else
{
uint8_t x_919; 
lean_dec(x_885);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_919 = !lean_is_exclusive(x_887);
if (x_919 == 0)
{
return x_887;
}
else
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_920 = lean_ctor_get(x_887, 0);
x_921 = lean_ctor_get(x_887, 1);
lean_inc(x_921);
lean_inc(x_920);
lean_dec(x_887);
x_922 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_922, 0, x_920);
lean_ctor_set(x_922, 1, x_921);
return x_922;
}
}
}
case 8:
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; 
x_923 = lean_ctor_get(x_5, 1);
lean_inc(x_923);
x_924 = lean_ctor_get(x_5, 2);
lean_inc(x_924);
x_925 = lean_ctor_get(x_5, 3);
lean_inc(x_925);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_926 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_923, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_926) == 0)
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; 
x_927 = lean_ctor_get(x_926, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_926, 1);
lean_inc(x_928);
lean_dec(x_926);
x_929 = lean_ctor_get(x_927, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_927, 1);
lean_inc(x_930);
lean_dec(x_927);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_931 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_924, x_6, x_930, x_8, x_928);
if (lean_obj_tag(x_931) == 0)
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_932 = lean_ctor_get(x_931, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_931, 1);
lean_inc(x_933);
lean_dec(x_931);
x_934 = lean_ctor_get(x_932, 0);
lean_inc(x_934);
x_935 = lean_ctor_get(x_932, 1);
lean_inc(x_935);
lean_dec(x_932);
x_936 = lean_unsigned_to_nat(1u);
x_937 = lean_nat_add(x_6, x_936);
lean_dec(x_6);
x_938 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_925, x_937, x_935, x_8, x_933);
if (lean_obj_tag(x_938) == 0)
{
uint8_t x_939; 
x_939 = !lean_is_exclusive(x_938);
if (x_939 == 0)
{
lean_object* x_940; uint8_t x_941; 
x_940 = lean_ctor_get(x_938, 0);
x_941 = !lean_is_exclusive(x_940);
if (x_941 == 0)
{
lean_object* x_942; lean_object* x_943; 
x_942 = lean_ctor_get(x_940, 0);
x_943 = lean_expr_update_let(x_5, x_929, x_934, x_942);
lean_ctor_set(x_940, 0, x_943);
return x_938;
}
else
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; 
x_944 = lean_ctor_get(x_940, 0);
x_945 = lean_ctor_get(x_940, 1);
lean_inc(x_945);
lean_inc(x_944);
lean_dec(x_940);
x_946 = lean_expr_update_let(x_5, x_929, x_934, x_944);
x_947 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_947, 0, x_946);
lean_ctor_set(x_947, 1, x_945);
lean_ctor_set(x_938, 0, x_947);
return x_938;
}
}
else
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; 
x_948 = lean_ctor_get(x_938, 0);
x_949 = lean_ctor_get(x_938, 1);
lean_inc(x_949);
lean_inc(x_948);
lean_dec(x_938);
x_950 = lean_ctor_get(x_948, 0);
lean_inc(x_950);
x_951 = lean_ctor_get(x_948, 1);
lean_inc(x_951);
if (lean_is_exclusive(x_948)) {
 lean_ctor_release(x_948, 0);
 lean_ctor_release(x_948, 1);
 x_952 = x_948;
} else {
 lean_dec_ref(x_948);
 x_952 = lean_box(0);
}
x_953 = lean_expr_update_let(x_5, x_929, x_934, x_950);
if (lean_is_scalar(x_952)) {
 x_954 = lean_alloc_ctor(0, 2, 0);
} else {
 x_954 = x_952;
}
lean_ctor_set(x_954, 0, x_953);
lean_ctor_set(x_954, 1, x_951);
x_955 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_955, 0, x_954);
lean_ctor_set(x_955, 1, x_949);
return x_955;
}
}
else
{
uint8_t x_956; 
lean_dec(x_934);
lean_dec(x_929);
lean_dec(x_5);
x_956 = !lean_is_exclusive(x_938);
if (x_956 == 0)
{
return x_938;
}
else
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; 
x_957 = lean_ctor_get(x_938, 0);
x_958 = lean_ctor_get(x_938, 1);
lean_inc(x_958);
lean_inc(x_957);
lean_dec(x_938);
x_959 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_959, 0, x_957);
lean_ctor_set(x_959, 1, x_958);
return x_959;
}
}
}
else
{
uint8_t x_960; 
lean_dec(x_929);
lean_dec(x_925);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_960 = !lean_is_exclusive(x_931);
if (x_960 == 0)
{
return x_931;
}
else
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; 
x_961 = lean_ctor_get(x_931, 0);
x_962 = lean_ctor_get(x_931, 1);
lean_inc(x_962);
lean_inc(x_961);
lean_dec(x_931);
x_963 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_963, 0, x_961);
lean_ctor_set(x_963, 1, x_962);
return x_963;
}
}
}
else
{
uint8_t x_964; 
lean_dec(x_925);
lean_dec(x_924);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_964 = !lean_is_exclusive(x_926);
if (x_964 == 0)
{
return x_926;
}
else
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; 
x_965 = lean_ctor_get(x_926, 0);
x_966 = lean_ctor_get(x_926, 1);
lean_inc(x_966);
lean_inc(x_965);
lean_dec(x_926);
x_967 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_967, 0, x_965);
lean_ctor_set(x_967, 1, x_966);
return x_967;
}
}
}
case 10:
{
lean_object* x_968; lean_object* x_969; 
x_968 = lean_ctor_get(x_5, 1);
lean_inc(x_968);
x_969 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_968, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_969) == 0)
{
uint8_t x_970; 
x_970 = !lean_is_exclusive(x_969);
if (x_970 == 0)
{
lean_object* x_971; uint8_t x_972; 
x_971 = lean_ctor_get(x_969, 0);
x_972 = !lean_is_exclusive(x_971);
if (x_972 == 0)
{
lean_object* x_973; lean_object* x_974; 
x_973 = lean_ctor_get(x_971, 0);
x_974 = lean_expr_update_mdata(x_5, x_973);
lean_ctor_set(x_971, 0, x_974);
return x_969;
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; 
x_975 = lean_ctor_get(x_971, 0);
x_976 = lean_ctor_get(x_971, 1);
lean_inc(x_976);
lean_inc(x_975);
lean_dec(x_971);
x_977 = lean_expr_update_mdata(x_5, x_975);
x_978 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_978, 0, x_977);
lean_ctor_set(x_978, 1, x_976);
lean_ctor_set(x_969, 0, x_978);
return x_969;
}
}
else
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; 
x_979 = lean_ctor_get(x_969, 0);
x_980 = lean_ctor_get(x_969, 1);
lean_inc(x_980);
lean_inc(x_979);
lean_dec(x_969);
x_981 = lean_ctor_get(x_979, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_979, 1);
lean_inc(x_982);
if (lean_is_exclusive(x_979)) {
 lean_ctor_release(x_979, 0);
 lean_ctor_release(x_979, 1);
 x_983 = x_979;
} else {
 lean_dec_ref(x_979);
 x_983 = lean_box(0);
}
x_984 = lean_expr_update_mdata(x_5, x_981);
if (lean_is_scalar(x_983)) {
 x_985 = lean_alloc_ctor(0, 2, 0);
} else {
 x_985 = x_983;
}
lean_ctor_set(x_985, 0, x_984);
lean_ctor_set(x_985, 1, x_982);
x_986 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_986, 0, x_985);
lean_ctor_set(x_986, 1, x_980);
return x_986;
}
}
else
{
uint8_t x_987; 
lean_dec(x_5);
x_987 = !lean_is_exclusive(x_969);
if (x_987 == 0)
{
return x_969;
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; 
x_988 = lean_ctor_get(x_969, 0);
x_989 = lean_ctor_get(x_969, 1);
lean_inc(x_989);
lean_inc(x_988);
lean_dec(x_969);
x_990 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_990, 0, x_988);
lean_ctor_set(x_990, 1, x_989);
return x_990;
}
}
}
case 11:
{
lean_object* x_991; lean_object* x_992; 
x_991 = lean_ctor_get(x_5, 2);
lean_inc(x_991);
x_992 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_991, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_992) == 0)
{
uint8_t x_993; 
x_993 = !lean_is_exclusive(x_992);
if (x_993 == 0)
{
lean_object* x_994; uint8_t x_995; 
x_994 = lean_ctor_get(x_992, 0);
x_995 = !lean_is_exclusive(x_994);
if (x_995 == 0)
{
lean_object* x_996; lean_object* x_997; 
x_996 = lean_ctor_get(x_994, 0);
x_997 = lean_expr_update_proj(x_5, x_996);
lean_ctor_set(x_994, 0, x_997);
return x_992;
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
x_998 = lean_ctor_get(x_994, 0);
x_999 = lean_ctor_get(x_994, 1);
lean_inc(x_999);
lean_inc(x_998);
lean_dec(x_994);
x_1000 = lean_expr_update_proj(x_5, x_998);
x_1001 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1001, 0, x_1000);
lean_ctor_set(x_1001, 1, x_999);
lean_ctor_set(x_992, 0, x_1001);
return x_992;
}
}
else
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
x_1002 = lean_ctor_get(x_992, 0);
x_1003 = lean_ctor_get(x_992, 1);
lean_inc(x_1003);
lean_inc(x_1002);
lean_dec(x_992);
x_1004 = lean_ctor_get(x_1002, 0);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_1002, 1);
lean_inc(x_1005);
if (lean_is_exclusive(x_1002)) {
 lean_ctor_release(x_1002, 0);
 lean_ctor_release(x_1002, 1);
 x_1006 = x_1002;
} else {
 lean_dec_ref(x_1002);
 x_1006 = lean_box(0);
}
x_1007 = lean_expr_update_proj(x_5, x_1004);
if (lean_is_scalar(x_1006)) {
 x_1008 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1008 = x_1006;
}
lean_ctor_set(x_1008, 0, x_1007);
lean_ctor_set(x_1008, 1, x_1005);
x_1009 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1009, 0, x_1008);
lean_ctor_set(x_1009, 1, x_1003);
return x_1009;
}
}
else
{
uint8_t x_1010; 
lean_dec(x_5);
x_1010 = !lean_is_exclusive(x_992);
if (x_1010 == 0)
{
return x_992;
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_1011 = lean_ctor_get(x_992, 0);
x_1012 = lean_ctor_get(x_992, 1);
lean_inc(x_1012);
lean_inc(x_1011);
lean_dec(x_992);
x_1013 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1013, 0, x_1011);
lean_ctor_set(x_1013, 1, x_1012);
return x_1013;
}
}
}
default: 
{
lean_object* x_1014; lean_object* x_1015; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_1014 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1014, 0, x_5);
lean_ctor_set(x_1014, 1, x_7);
x_1015 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1015, 0, x_1014);
lean_ctor_set(x_1015, 1, x_9);
return x_1015;
}
}
}
block_803:
{
uint8_t x_11; 
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_14 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_13, x_6, x_18, x_8, x_16);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_expr_update_app(x_5, x_17, x_23);
lean_ctor_set(x_21, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_expr_update_app(x_5, x_17, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_33 = x_29;
} else {
 lean_dec_ref(x_29);
 x_33 = lean_box(0);
}
x_34 = lean_expr_update_app(x_5, x_17, x_31);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_17);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_19);
if (x_37 == 0)
{
return x_19;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_19);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_14);
if (x_41 == 0)
{
return x_14;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_14, 0);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_14);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
case 6:
{
lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_5, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_5, 2);
lean_inc(x_46);
x_47 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_48 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_45, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_6, x_53);
lean_dec(x_6);
x_55 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_46, x_54, x_52, x_8, x_50);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = (uint8_t)((x_47 << 24) >> 61);
x_61 = lean_expr_update_lambda(x_5, x_60, x_51, x_59);
lean_ctor_set(x_57, 0, x_61);
return x_55;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_57);
x_64 = (uint8_t)((x_47 << 24) >> 61);
x_65 = lean_expr_update_lambda(x_5, x_64, x_51, x_62);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
lean_ctor_set(x_55, 0, x_66);
return x_55;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_55, 0);
x_68 = lean_ctor_get(x_55, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_55);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_71 = x_67;
} else {
 lean_dec_ref(x_67);
 x_71 = lean_box(0);
}
x_72 = (uint8_t)((x_47 << 24) >> 61);
x_73 = lean_expr_update_lambda(x_5, x_72, x_51, x_69);
if (lean_is_scalar(x_71)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_71;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_68);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_51);
lean_dec(x_5);
x_76 = !lean_is_exclusive(x_55);
if (x_76 == 0)
{
return x_55;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_55, 0);
x_78 = lean_ctor_get(x_55, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_55);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_46);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_80 = !lean_is_exclusive(x_48);
if (x_80 == 0)
{
return x_48;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_48, 0);
x_82 = lean_ctor_get(x_48, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_48);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
case 7:
{
lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_5, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_5, 2);
lean_inc(x_85);
x_86 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_87 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_84, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_add(x_6, x_92);
lean_dec(x_6);
x_94 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_85, x_93, x_91, x_8, x_89);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = (uint8_t)((x_86 << 24) >> 61);
x_100 = lean_expr_update_forall(x_5, x_99, x_90, x_98);
lean_ctor_set(x_96, 0, x_100);
return x_94;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_96, 0);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_96);
x_103 = (uint8_t)((x_86 << 24) >> 61);
x_104 = lean_expr_update_forall(x_5, x_103, x_90, x_101);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_102);
lean_ctor_set(x_94, 0, x_105);
return x_94;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_106 = lean_ctor_get(x_94, 0);
x_107 = lean_ctor_get(x_94, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_94);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_110 = x_106;
} else {
 lean_dec_ref(x_106);
 x_110 = lean_box(0);
}
x_111 = (uint8_t)((x_86 << 24) >> 61);
x_112 = lean_expr_update_forall(x_5, x_111, x_90, x_108);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_109);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_107);
return x_114;
}
}
else
{
uint8_t x_115; 
lean_dec(x_90);
lean_dec(x_5);
x_115 = !lean_is_exclusive(x_94);
if (x_115 == 0)
{
return x_94;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_94, 0);
x_117 = lean_ctor_get(x_94, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_94);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_85);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_119 = !lean_is_exclusive(x_87);
if (x_119 == 0)
{
return x_87;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_87, 0);
x_121 = lean_ctor_get(x_87, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_87);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
case 8:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_5, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_5, 2);
lean_inc(x_124);
x_125 = lean_ctor_get(x_5, 3);
lean_inc(x_125);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_126 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_123, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_131 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_124, x_6, x_130, x_8, x_128);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec(x_132);
x_136 = lean_unsigned_to_nat(1u);
x_137 = lean_nat_add(x_6, x_136);
lean_dec(x_6);
x_138 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_125, x_137, x_135, x_8, x_133);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = lean_expr_update_let(x_5, x_129, x_134, x_142);
lean_ctor_set(x_140, 0, x_143);
return x_138;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_140, 0);
x_145 = lean_ctor_get(x_140, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_140);
x_146 = lean_expr_update_let(x_5, x_129, x_134, x_144);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
lean_ctor_set(x_138, 0, x_147);
return x_138;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_148 = lean_ctor_get(x_138, 0);
x_149 = lean_ctor_get(x_138, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_138);
x_150 = lean_ctor_get(x_148, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_148, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_152 = x_148;
} else {
 lean_dec_ref(x_148);
 x_152 = lean_box(0);
}
x_153 = lean_expr_update_let(x_5, x_129, x_134, x_150);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_149);
return x_155;
}
}
else
{
uint8_t x_156; 
lean_dec(x_134);
lean_dec(x_129);
lean_dec(x_5);
x_156 = !lean_is_exclusive(x_138);
if (x_156 == 0)
{
return x_138;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_138, 0);
x_158 = lean_ctor_get(x_138, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_138);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_129);
lean_dec(x_125);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_160 = !lean_is_exclusive(x_131);
if (x_160 == 0)
{
return x_131;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_131, 0);
x_162 = lean_ctor_get(x_131, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_131);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_126);
if (x_164 == 0)
{
return x_126;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_126, 0);
x_166 = lean_ctor_get(x_126, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_126);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
case 10:
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_5, 1);
lean_inc(x_168);
x_169 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_168, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_169) == 0)
{
uint8_t x_170; 
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_171, 0);
x_174 = lean_expr_update_mdata(x_5, x_173);
lean_ctor_set(x_171, 0, x_174);
return x_169;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_175 = lean_ctor_get(x_171, 0);
x_176 = lean_ctor_get(x_171, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_171);
x_177 = lean_expr_update_mdata(x_5, x_175);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
lean_ctor_set(x_169, 0, x_178);
return x_169;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_179 = lean_ctor_get(x_169, 0);
x_180 = lean_ctor_get(x_169, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_169);
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_183 = x_179;
} else {
 lean_dec_ref(x_179);
 x_183 = lean_box(0);
}
x_184 = lean_expr_update_mdata(x_5, x_181);
if (lean_is_scalar(x_183)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_183;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_182);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_180);
return x_186;
}
}
else
{
uint8_t x_187; 
lean_dec(x_5);
x_187 = !lean_is_exclusive(x_169);
if (x_187 == 0)
{
return x_169;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_169, 0);
x_189 = lean_ctor_get(x_169, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_169);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
case 11:
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_5, 2);
lean_inc(x_191);
x_192 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_191, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_192) == 0)
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
lean_object* x_194; uint8_t x_195; 
x_194 = lean_ctor_get(x_192, 0);
x_195 = !lean_is_exclusive(x_194);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_194, 0);
x_197 = lean_expr_update_proj(x_5, x_196);
lean_ctor_set(x_194, 0, x_197);
return x_192;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_194, 0);
x_199 = lean_ctor_get(x_194, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_194);
x_200 = lean_expr_update_proj(x_5, x_198);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_192, 0, x_201);
return x_192;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_202 = lean_ctor_get(x_192, 0);
x_203 = lean_ctor_get(x_192, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_192);
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_206 = x_202;
} else {
 lean_dec_ref(x_202);
 x_206 = lean_box(0);
}
x_207 = lean_expr_update_proj(x_5, x_204);
if (lean_is_scalar(x_206)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_206;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_205);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_203);
return x_209;
}
}
else
{
uint8_t x_210; 
lean_dec(x_5);
x_210 = !lean_is_exclusive(x_192);
if (x_210 == 0)
{
return x_192;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_192, 0);
x_212 = lean_ctor_get(x_192, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_192);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
default: 
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_5);
lean_ctor_set(x_214, 1, x_7);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_9);
return x_215;
}
}
}
else
{
lean_object* x_216; 
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_5);
x_216 = l_Lean_Meta_isExprDefEq(x_5, x_2, x_8, x_9);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; uint8_t x_218; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_unbox(x_217);
lean_dec(x_217);
if (x_218 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_dec(x_216);
x_220 = lean_ctor_get(x_5, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_5, 1);
lean_inc(x_221);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_222 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_220, x_6, x_7, x_8, x_219);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_ctor_get(x_223, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_223, 1);
lean_inc(x_226);
lean_dec(x_223);
x_227 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_221, x_6, x_226, x_8, x_224);
if (lean_obj_tag(x_227) == 0)
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
lean_object* x_229; uint8_t x_230; 
x_229 = lean_ctor_get(x_227, 0);
x_230 = !lean_is_exclusive(x_229);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_229, 0);
x_232 = lean_expr_update_app(x_5, x_225, x_231);
lean_ctor_set(x_229, 0, x_232);
return x_227;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_229, 0);
x_234 = lean_ctor_get(x_229, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_229);
x_235 = lean_expr_update_app(x_5, x_225, x_233);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_234);
lean_ctor_set(x_227, 0, x_236);
return x_227;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_237 = lean_ctor_get(x_227, 0);
x_238 = lean_ctor_get(x_227, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_227);
x_239 = lean_ctor_get(x_237, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_241 = x_237;
} else {
 lean_dec_ref(x_237);
 x_241 = lean_box(0);
}
x_242 = lean_expr_update_app(x_5, x_225, x_239);
if (lean_is_scalar(x_241)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_241;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_240);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_238);
return x_244;
}
}
else
{
uint8_t x_245; 
lean_dec(x_225);
lean_dec(x_5);
x_245 = !lean_is_exclusive(x_227);
if (x_245 == 0)
{
return x_227;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_227, 0);
x_247 = lean_ctor_get(x_227, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_227);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_221);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_249 = !lean_is_exclusive(x_222);
if (x_249 == 0)
{
return x_222;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_222, 0);
x_251 = lean_ctor_get(x_222, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_222);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
case 6:
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; uint64_t x_256; lean_object* x_257; 
x_253 = lean_ctor_get(x_216, 1);
lean_inc(x_253);
lean_dec(x_216);
x_254 = lean_ctor_get(x_5, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_5, 2);
lean_inc(x_255);
x_256 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_257 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_254, x_6, x_7, x_8, x_253);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_ctor_get(x_258, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
lean_dec(x_258);
x_262 = lean_unsigned_to_nat(1u);
x_263 = lean_nat_add(x_6, x_262);
lean_dec(x_6);
x_264 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_255, x_263, x_261, x_8, x_259);
if (lean_obj_tag(x_264) == 0)
{
uint8_t x_265; 
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
lean_object* x_266; uint8_t x_267; 
x_266 = lean_ctor_get(x_264, 0);
x_267 = !lean_is_exclusive(x_266);
if (x_267 == 0)
{
lean_object* x_268; uint8_t x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_266, 0);
x_269 = (uint8_t)((x_256 << 24) >> 61);
x_270 = lean_expr_update_lambda(x_5, x_269, x_260, x_268);
lean_ctor_set(x_266, 0, x_270);
return x_264;
}
else
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; 
x_271 = lean_ctor_get(x_266, 0);
x_272 = lean_ctor_get(x_266, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_266);
x_273 = (uint8_t)((x_256 << 24) >> 61);
x_274 = lean_expr_update_lambda(x_5, x_273, x_260, x_271);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_272);
lean_ctor_set(x_264, 0, x_275);
return x_264;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_276 = lean_ctor_get(x_264, 0);
x_277 = lean_ctor_get(x_264, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_264);
x_278 = lean_ctor_get(x_276, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_280 = x_276;
} else {
 lean_dec_ref(x_276);
 x_280 = lean_box(0);
}
x_281 = (uint8_t)((x_256 << 24) >> 61);
x_282 = lean_expr_update_lambda(x_5, x_281, x_260, x_278);
if (lean_is_scalar(x_280)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_280;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_279);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_277);
return x_284;
}
}
else
{
uint8_t x_285; 
lean_dec(x_260);
lean_dec(x_5);
x_285 = !lean_is_exclusive(x_264);
if (x_285 == 0)
{
return x_264;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_264, 0);
x_287 = lean_ctor_get(x_264, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_264);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
}
else
{
uint8_t x_289; 
lean_dec(x_255);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_289 = !lean_is_exclusive(x_257);
if (x_289 == 0)
{
return x_257;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_257, 0);
x_291 = lean_ctor_get(x_257, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_257);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
case 7:
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; uint64_t x_296; lean_object* x_297; 
x_293 = lean_ctor_get(x_216, 1);
lean_inc(x_293);
lean_dec(x_216);
x_294 = lean_ctor_get(x_5, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_5, 2);
lean_inc(x_295);
x_296 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_297 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_294, x_6, x_7, x_8, x_293);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_ctor_get(x_298, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_302 = lean_unsigned_to_nat(1u);
x_303 = lean_nat_add(x_6, x_302);
lean_dec(x_6);
x_304 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_295, x_303, x_301, x_8, x_299);
if (lean_obj_tag(x_304) == 0)
{
uint8_t x_305; 
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; uint8_t x_307; 
x_306 = lean_ctor_get(x_304, 0);
x_307 = !lean_is_exclusive(x_306);
if (x_307 == 0)
{
lean_object* x_308; uint8_t x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_306, 0);
x_309 = (uint8_t)((x_296 << 24) >> 61);
x_310 = lean_expr_update_forall(x_5, x_309, x_300, x_308);
lean_ctor_set(x_306, 0, x_310);
return x_304;
}
else
{
lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; 
x_311 = lean_ctor_get(x_306, 0);
x_312 = lean_ctor_get(x_306, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_306);
x_313 = (uint8_t)((x_296 << 24) >> 61);
x_314 = lean_expr_update_forall(x_5, x_313, x_300, x_311);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_312);
lean_ctor_set(x_304, 0, x_315);
return x_304;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_316 = lean_ctor_get(x_304, 0);
x_317 = lean_ctor_get(x_304, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_304);
x_318 = lean_ctor_get(x_316, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_316, 1);
lean_inc(x_319);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_320 = x_316;
} else {
 lean_dec_ref(x_316);
 x_320 = lean_box(0);
}
x_321 = (uint8_t)((x_296 << 24) >> 61);
x_322 = lean_expr_update_forall(x_5, x_321, x_300, x_318);
if (lean_is_scalar(x_320)) {
 x_323 = lean_alloc_ctor(0, 2, 0);
} else {
 x_323 = x_320;
}
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_319);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_317);
return x_324;
}
}
else
{
uint8_t x_325; 
lean_dec(x_300);
lean_dec(x_5);
x_325 = !lean_is_exclusive(x_304);
if (x_325 == 0)
{
return x_304;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_304, 0);
x_327 = lean_ctor_get(x_304, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_304);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
else
{
uint8_t x_329; 
lean_dec(x_295);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_329 = !lean_is_exclusive(x_297);
if (x_329 == 0)
{
return x_297;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_297, 0);
x_331 = lean_ctor_get(x_297, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_297);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
}
case 8:
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_333 = lean_ctor_get(x_216, 1);
lean_inc(x_333);
lean_dec(x_216);
x_334 = lean_ctor_get(x_5, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_5, 2);
lean_inc(x_335);
x_336 = lean_ctor_get(x_5, 3);
lean_inc(x_336);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_337 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_334, x_6, x_7, x_8, x_333);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_ctor_get(x_338, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
lean_dec(x_338);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_342 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_335, x_6, x_341, x_8, x_339);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = lean_ctor_get(x_343, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_343, 1);
lean_inc(x_346);
lean_dec(x_343);
x_347 = lean_unsigned_to_nat(1u);
x_348 = lean_nat_add(x_6, x_347);
lean_dec(x_6);
x_349 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_336, x_348, x_346, x_8, x_344);
if (lean_obj_tag(x_349) == 0)
{
uint8_t x_350; 
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
lean_object* x_351; uint8_t x_352; 
x_351 = lean_ctor_get(x_349, 0);
x_352 = !lean_is_exclusive(x_351);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_ctor_get(x_351, 0);
x_354 = lean_expr_update_let(x_5, x_340, x_345, x_353);
lean_ctor_set(x_351, 0, x_354);
return x_349;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_355 = lean_ctor_get(x_351, 0);
x_356 = lean_ctor_get(x_351, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_351);
x_357 = lean_expr_update_let(x_5, x_340, x_345, x_355);
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set(x_358, 1, x_356);
lean_ctor_set(x_349, 0, x_358);
return x_349;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_359 = lean_ctor_get(x_349, 0);
x_360 = lean_ctor_get(x_349, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_349);
x_361 = lean_ctor_get(x_359, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_359, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_363 = x_359;
} else {
 lean_dec_ref(x_359);
 x_363 = lean_box(0);
}
x_364 = lean_expr_update_let(x_5, x_340, x_345, x_361);
if (lean_is_scalar(x_363)) {
 x_365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_365 = x_363;
}
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_362);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_360);
return x_366;
}
}
else
{
uint8_t x_367; 
lean_dec(x_345);
lean_dec(x_340);
lean_dec(x_5);
x_367 = !lean_is_exclusive(x_349);
if (x_367 == 0)
{
return x_349;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_349, 0);
x_369 = lean_ctor_get(x_349, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_349);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
return x_370;
}
}
}
else
{
uint8_t x_371; 
lean_dec(x_340);
lean_dec(x_336);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_371 = !lean_is_exclusive(x_342);
if (x_371 == 0)
{
return x_342;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_342, 0);
x_373 = lean_ctor_get(x_342, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_342);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
return x_374;
}
}
}
else
{
uint8_t x_375; 
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_375 = !lean_is_exclusive(x_337);
if (x_375 == 0)
{
return x_337;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_337, 0);
x_377 = lean_ctor_get(x_337, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_337);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
case 10:
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_216, 1);
lean_inc(x_379);
lean_dec(x_216);
x_380 = lean_ctor_get(x_5, 1);
lean_inc(x_380);
x_381 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_380, x_6, x_7, x_8, x_379);
if (lean_obj_tag(x_381) == 0)
{
uint8_t x_382; 
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
lean_object* x_383; uint8_t x_384; 
x_383 = lean_ctor_get(x_381, 0);
x_384 = !lean_is_exclusive(x_383);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; 
x_385 = lean_ctor_get(x_383, 0);
x_386 = lean_expr_update_mdata(x_5, x_385);
lean_ctor_set(x_383, 0, x_386);
return x_381;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_387 = lean_ctor_get(x_383, 0);
x_388 = lean_ctor_get(x_383, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_383);
x_389 = lean_expr_update_mdata(x_5, x_387);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_388);
lean_ctor_set(x_381, 0, x_390);
return x_381;
}
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_391 = lean_ctor_get(x_381, 0);
x_392 = lean_ctor_get(x_381, 1);
lean_inc(x_392);
lean_inc(x_391);
lean_dec(x_381);
x_393 = lean_ctor_get(x_391, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_391, 1);
lean_inc(x_394);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_395 = x_391;
} else {
 lean_dec_ref(x_391);
 x_395 = lean_box(0);
}
x_396 = lean_expr_update_mdata(x_5, x_393);
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_394);
x_398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_392);
return x_398;
}
}
else
{
uint8_t x_399; 
lean_dec(x_5);
x_399 = !lean_is_exclusive(x_381);
if (x_399 == 0)
{
return x_381;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_381, 0);
x_401 = lean_ctor_get(x_381, 1);
lean_inc(x_401);
lean_inc(x_400);
lean_dec(x_381);
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
return x_402;
}
}
}
case 11:
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_403 = lean_ctor_get(x_216, 1);
lean_inc(x_403);
lean_dec(x_216);
x_404 = lean_ctor_get(x_5, 2);
lean_inc(x_404);
x_405 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_404, x_6, x_7, x_8, x_403);
if (lean_obj_tag(x_405) == 0)
{
uint8_t x_406; 
x_406 = !lean_is_exclusive(x_405);
if (x_406 == 0)
{
lean_object* x_407; uint8_t x_408; 
x_407 = lean_ctor_get(x_405, 0);
x_408 = !lean_is_exclusive(x_407);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; 
x_409 = lean_ctor_get(x_407, 0);
x_410 = lean_expr_update_proj(x_5, x_409);
lean_ctor_set(x_407, 0, x_410);
return x_405;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_411 = lean_ctor_get(x_407, 0);
x_412 = lean_ctor_get(x_407, 1);
lean_inc(x_412);
lean_inc(x_411);
lean_dec(x_407);
x_413 = lean_expr_update_proj(x_5, x_411);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_412);
lean_ctor_set(x_405, 0, x_414);
return x_405;
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_415 = lean_ctor_get(x_405, 0);
x_416 = lean_ctor_get(x_405, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_405);
x_417 = lean_ctor_get(x_415, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_415, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_419 = x_415;
} else {
 lean_dec_ref(x_415);
 x_419 = lean_box(0);
}
x_420 = lean_expr_update_proj(x_5, x_417);
if (lean_is_scalar(x_419)) {
 x_421 = lean_alloc_ctor(0, 2, 0);
} else {
 x_421 = x_419;
}
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_418);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_416);
return x_422;
}
}
else
{
uint8_t x_423; 
lean_dec(x_5);
x_423 = !lean_is_exclusive(x_405);
if (x_423 == 0)
{
return x_405;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_405, 0);
x_425 = lean_ctor_get(x_405, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_405);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
}
default: 
{
uint8_t x_427; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_427 = !lean_is_exclusive(x_216);
if (x_427 == 0)
{
lean_object* x_428; lean_object* x_429; 
x_428 = lean_ctor_get(x_216, 0);
lean_dec(x_428);
x_429 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_429, 0, x_5);
lean_ctor_set(x_429, 1, x_7);
lean_ctor_set(x_216, 0, x_429);
return x_216;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_216, 1);
lean_inc(x_430);
lean_dec(x_216);
x_431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_431, 0, x_5);
lean_ctor_set(x_431, 1, x_7);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_430);
return x_432;
}
}
}
}
else
{
uint8_t x_433; 
x_433 = !lean_is_exclusive(x_216);
if (x_433 == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; uint8_t x_439; 
x_434 = lean_ctor_get(x_216, 1);
x_435 = lean_ctor_get(x_216, 0);
lean_dec(x_435);
x_436 = lean_unsigned_to_nat(1u);
x_437 = lean_nat_add(x_7, x_436);
x_438 = l_Lean_Occurrences_contains(x_1, x_7);
lean_dec(x_7);
x_439 = l_coeDecidableEq(x_438);
if (x_439 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_free_object(x_216);
x_440 = lean_ctor_get(x_5, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_5, 1);
lean_inc(x_441);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_442 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_440, x_6, x_437, x_8, x_434);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
x_445 = lean_ctor_get(x_443, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_443, 1);
lean_inc(x_446);
lean_dec(x_443);
x_447 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_441, x_6, x_446, x_8, x_444);
if (lean_obj_tag(x_447) == 0)
{
uint8_t x_448; 
x_448 = !lean_is_exclusive(x_447);
if (x_448 == 0)
{
lean_object* x_449; uint8_t x_450; 
x_449 = lean_ctor_get(x_447, 0);
x_450 = !lean_is_exclusive(x_449);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; 
x_451 = lean_ctor_get(x_449, 0);
x_452 = lean_expr_update_app(x_5, x_445, x_451);
lean_ctor_set(x_449, 0, x_452);
return x_447;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_453 = lean_ctor_get(x_449, 0);
x_454 = lean_ctor_get(x_449, 1);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_449);
x_455 = lean_expr_update_app(x_5, x_445, x_453);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_454);
lean_ctor_set(x_447, 0, x_456);
return x_447;
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_457 = lean_ctor_get(x_447, 0);
x_458 = lean_ctor_get(x_447, 1);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_447);
x_459 = lean_ctor_get(x_457, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_457, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 x_461 = x_457;
} else {
 lean_dec_ref(x_457);
 x_461 = lean_box(0);
}
x_462 = lean_expr_update_app(x_5, x_445, x_459);
if (lean_is_scalar(x_461)) {
 x_463 = lean_alloc_ctor(0, 2, 0);
} else {
 x_463 = x_461;
}
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_460);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_458);
return x_464;
}
}
else
{
uint8_t x_465; 
lean_dec(x_445);
lean_dec(x_5);
x_465 = !lean_is_exclusive(x_447);
if (x_465 == 0)
{
return x_447;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_466 = lean_ctor_get(x_447, 0);
x_467 = lean_ctor_get(x_447, 1);
lean_inc(x_467);
lean_inc(x_466);
lean_dec(x_447);
x_468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set(x_468, 1, x_467);
return x_468;
}
}
}
else
{
uint8_t x_469; 
lean_dec(x_441);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_469 = !lean_is_exclusive(x_442);
if (x_469 == 0)
{
return x_442;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_ctor_get(x_442, 0);
x_471 = lean_ctor_get(x_442, 1);
lean_inc(x_471);
lean_inc(x_470);
lean_dec(x_442);
x_472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_471);
return x_472;
}
}
}
case 6:
{
lean_object* x_473; lean_object* x_474; uint64_t x_475; lean_object* x_476; 
lean_free_object(x_216);
x_473 = lean_ctor_get(x_5, 1);
lean_inc(x_473);
x_474 = lean_ctor_get(x_5, 2);
lean_inc(x_474);
x_475 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_476 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_473, x_6, x_437, x_8, x_434);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
lean_dec(x_476);
x_479 = lean_ctor_get(x_477, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_477, 1);
lean_inc(x_480);
lean_dec(x_477);
x_481 = lean_nat_add(x_6, x_436);
lean_dec(x_6);
x_482 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_474, x_481, x_480, x_8, x_478);
if (lean_obj_tag(x_482) == 0)
{
uint8_t x_483; 
x_483 = !lean_is_exclusive(x_482);
if (x_483 == 0)
{
lean_object* x_484; uint8_t x_485; 
x_484 = lean_ctor_get(x_482, 0);
x_485 = !lean_is_exclusive(x_484);
if (x_485 == 0)
{
lean_object* x_486; uint8_t x_487; lean_object* x_488; 
x_486 = lean_ctor_get(x_484, 0);
x_487 = (uint8_t)((x_475 << 24) >> 61);
x_488 = lean_expr_update_lambda(x_5, x_487, x_479, x_486);
lean_ctor_set(x_484, 0, x_488);
return x_482;
}
else
{
lean_object* x_489; lean_object* x_490; uint8_t x_491; lean_object* x_492; lean_object* x_493; 
x_489 = lean_ctor_get(x_484, 0);
x_490 = lean_ctor_get(x_484, 1);
lean_inc(x_490);
lean_inc(x_489);
lean_dec(x_484);
x_491 = (uint8_t)((x_475 << 24) >> 61);
x_492 = lean_expr_update_lambda(x_5, x_491, x_479, x_489);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_490);
lean_ctor_set(x_482, 0, x_493);
return x_482;
}
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_494 = lean_ctor_get(x_482, 0);
x_495 = lean_ctor_get(x_482, 1);
lean_inc(x_495);
lean_inc(x_494);
lean_dec(x_482);
x_496 = lean_ctor_get(x_494, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_494, 1);
lean_inc(x_497);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_498 = x_494;
} else {
 lean_dec_ref(x_494);
 x_498 = lean_box(0);
}
x_499 = (uint8_t)((x_475 << 24) >> 61);
x_500 = lean_expr_update_lambda(x_5, x_499, x_479, x_496);
if (lean_is_scalar(x_498)) {
 x_501 = lean_alloc_ctor(0, 2, 0);
} else {
 x_501 = x_498;
}
lean_ctor_set(x_501, 0, x_500);
lean_ctor_set(x_501, 1, x_497);
x_502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_495);
return x_502;
}
}
else
{
uint8_t x_503; 
lean_dec(x_479);
lean_dec(x_5);
x_503 = !lean_is_exclusive(x_482);
if (x_503 == 0)
{
return x_482;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_482, 0);
x_505 = lean_ctor_get(x_482, 1);
lean_inc(x_505);
lean_inc(x_504);
lean_dec(x_482);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
return x_506;
}
}
}
else
{
uint8_t x_507; 
lean_dec(x_474);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_507 = !lean_is_exclusive(x_476);
if (x_507 == 0)
{
return x_476;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_508 = lean_ctor_get(x_476, 0);
x_509 = lean_ctor_get(x_476, 1);
lean_inc(x_509);
lean_inc(x_508);
lean_dec(x_476);
x_510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_510, 0, x_508);
lean_ctor_set(x_510, 1, x_509);
return x_510;
}
}
}
case 7:
{
lean_object* x_511; lean_object* x_512; uint64_t x_513; lean_object* x_514; 
lean_free_object(x_216);
x_511 = lean_ctor_get(x_5, 1);
lean_inc(x_511);
x_512 = lean_ctor_get(x_5, 2);
lean_inc(x_512);
x_513 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_514 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_511, x_6, x_437, x_8, x_434);
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_514, 1);
lean_inc(x_516);
lean_dec(x_514);
x_517 = lean_ctor_get(x_515, 0);
lean_inc(x_517);
x_518 = lean_ctor_get(x_515, 1);
lean_inc(x_518);
lean_dec(x_515);
x_519 = lean_nat_add(x_6, x_436);
lean_dec(x_6);
x_520 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_512, x_519, x_518, x_8, x_516);
if (lean_obj_tag(x_520) == 0)
{
uint8_t x_521; 
x_521 = !lean_is_exclusive(x_520);
if (x_521 == 0)
{
lean_object* x_522; uint8_t x_523; 
x_522 = lean_ctor_get(x_520, 0);
x_523 = !lean_is_exclusive(x_522);
if (x_523 == 0)
{
lean_object* x_524; uint8_t x_525; lean_object* x_526; 
x_524 = lean_ctor_get(x_522, 0);
x_525 = (uint8_t)((x_513 << 24) >> 61);
x_526 = lean_expr_update_forall(x_5, x_525, x_517, x_524);
lean_ctor_set(x_522, 0, x_526);
return x_520;
}
else
{
lean_object* x_527; lean_object* x_528; uint8_t x_529; lean_object* x_530; lean_object* x_531; 
x_527 = lean_ctor_get(x_522, 0);
x_528 = lean_ctor_get(x_522, 1);
lean_inc(x_528);
lean_inc(x_527);
lean_dec(x_522);
x_529 = (uint8_t)((x_513 << 24) >> 61);
x_530 = lean_expr_update_forall(x_5, x_529, x_517, x_527);
x_531 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_528);
lean_ctor_set(x_520, 0, x_531);
return x_520;
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_532 = lean_ctor_get(x_520, 0);
x_533 = lean_ctor_get(x_520, 1);
lean_inc(x_533);
lean_inc(x_532);
lean_dec(x_520);
x_534 = lean_ctor_get(x_532, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_532, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_536 = x_532;
} else {
 lean_dec_ref(x_532);
 x_536 = lean_box(0);
}
x_537 = (uint8_t)((x_513 << 24) >> 61);
x_538 = lean_expr_update_forall(x_5, x_537, x_517, x_534);
if (lean_is_scalar(x_536)) {
 x_539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_539 = x_536;
}
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_535);
x_540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_533);
return x_540;
}
}
else
{
uint8_t x_541; 
lean_dec(x_517);
lean_dec(x_5);
x_541 = !lean_is_exclusive(x_520);
if (x_541 == 0)
{
return x_520;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_ctor_get(x_520, 0);
x_543 = lean_ctor_get(x_520, 1);
lean_inc(x_543);
lean_inc(x_542);
lean_dec(x_520);
x_544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_543);
return x_544;
}
}
}
else
{
uint8_t x_545; 
lean_dec(x_512);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_545 = !lean_is_exclusive(x_514);
if (x_545 == 0)
{
return x_514;
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_546 = lean_ctor_get(x_514, 0);
x_547 = lean_ctor_get(x_514, 1);
lean_inc(x_547);
lean_inc(x_546);
lean_dec(x_514);
x_548 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set(x_548, 1, x_547);
return x_548;
}
}
}
case 8:
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_free_object(x_216);
x_549 = lean_ctor_get(x_5, 1);
lean_inc(x_549);
x_550 = lean_ctor_get(x_5, 2);
lean_inc(x_550);
x_551 = lean_ctor_get(x_5, 3);
lean_inc(x_551);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_552 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_549, x_6, x_437, x_8, x_434);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
lean_dec(x_552);
x_555 = lean_ctor_get(x_553, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_553, 1);
lean_inc(x_556);
lean_dec(x_553);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_557 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_550, x_6, x_556, x_8, x_554);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
lean_dec(x_557);
x_560 = lean_ctor_get(x_558, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_558, 1);
lean_inc(x_561);
lean_dec(x_558);
x_562 = lean_nat_add(x_6, x_436);
lean_dec(x_6);
x_563 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_551, x_562, x_561, x_8, x_559);
if (lean_obj_tag(x_563) == 0)
{
uint8_t x_564; 
x_564 = !lean_is_exclusive(x_563);
if (x_564 == 0)
{
lean_object* x_565; uint8_t x_566; 
x_565 = lean_ctor_get(x_563, 0);
x_566 = !lean_is_exclusive(x_565);
if (x_566 == 0)
{
lean_object* x_567; lean_object* x_568; 
x_567 = lean_ctor_get(x_565, 0);
x_568 = lean_expr_update_let(x_5, x_555, x_560, x_567);
lean_ctor_set(x_565, 0, x_568);
return x_563;
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_569 = lean_ctor_get(x_565, 0);
x_570 = lean_ctor_get(x_565, 1);
lean_inc(x_570);
lean_inc(x_569);
lean_dec(x_565);
x_571 = lean_expr_update_let(x_5, x_555, x_560, x_569);
x_572 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_572, 0, x_571);
lean_ctor_set(x_572, 1, x_570);
lean_ctor_set(x_563, 0, x_572);
return x_563;
}
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_573 = lean_ctor_get(x_563, 0);
x_574 = lean_ctor_get(x_563, 1);
lean_inc(x_574);
lean_inc(x_573);
lean_dec(x_563);
x_575 = lean_ctor_get(x_573, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_573, 1);
lean_inc(x_576);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 lean_ctor_release(x_573, 1);
 x_577 = x_573;
} else {
 lean_dec_ref(x_573);
 x_577 = lean_box(0);
}
x_578 = lean_expr_update_let(x_5, x_555, x_560, x_575);
if (lean_is_scalar(x_577)) {
 x_579 = lean_alloc_ctor(0, 2, 0);
} else {
 x_579 = x_577;
}
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set(x_579, 1, x_576);
x_580 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_580, 0, x_579);
lean_ctor_set(x_580, 1, x_574);
return x_580;
}
}
else
{
uint8_t x_581; 
lean_dec(x_560);
lean_dec(x_555);
lean_dec(x_5);
x_581 = !lean_is_exclusive(x_563);
if (x_581 == 0)
{
return x_563;
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_ctor_get(x_563, 0);
x_583 = lean_ctor_get(x_563, 1);
lean_inc(x_583);
lean_inc(x_582);
lean_dec(x_563);
x_584 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_584, 0, x_582);
lean_ctor_set(x_584, 1, x_583);
return x_584;
}
}
}
else
{
uint8_t x_585; 
lean_dec(x_555);
lean_dec(x_551);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_585 = !lean_is_exclusive(x_557);
if (x_585 == 0)
{
return x_557;
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_586 = lean_ctor_get(x_557, 0);
x_587 = lean_ctor_get(x_557, 1);
lean_inc(x_587);
lean_inc(x_586);
lean_dec(x_557);
x_588 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_588, 0, x_586);
lean_ctor_set(x_588, 1, x_587);
return x_588;
}
}
}
else
{
uint8_t x_589; 
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_589 = !lean_is_exclusive(x_552);
if (x_589 == 0)
{
return x_552;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_552, 0);
x_591 = lean_ctor_get(x_552, 1);
lean_inc(x_591);
lean_inc(x_590);
lean_dec(x_552);
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
return x_592;
}
}
}
case 10:
{
lean_object* x_593; lean_object* x_594; 
lean_free_object(x_216);
x_593 = lean_ctor_get(x_5, 1);
lean_inc(x_593);
x_594 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_593, x_6, x_437, x_8, x_434);
if (lean_obj_tag(x_594) == 0)
{
uint8_t x_595; 
x_595 = !lean_is_exclusive(x_594);
if (x_595 == 0)
{
lean_object* x_596; uint8_t x_597; 
x_596 = lean_ctor_get(x_594, 0);
x_597 = !lean_is_exclusive(x_596);
if (x_597 == 0)
{
lean_object* x_598; lean_object* x_599; 
x_598 = lean_ctor_get(x_596, 0);
x_599 = lean_expr_update_mdata(x_5, x_598);
lean_ctor_set(x_596, 0, x_599);
return x_594;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_600 = lean_ctor_get(x_596, 0);
x_601 = lean_ctor_get(x_596, 1);
lean_inc(x_601);
lean_inc(x_600);
lean_dec(x_596);
x_602 = lean_expr_update_mdata(x_5, x_600);
x_603 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_603, 0, x_602);
lean_ctor_set(x_603, 1, x_601);
lean_ctor_set(x_594, 0, x_603);
return x_594;
}
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_604 = lean_ctor_get(x_594, 0);
x_605 = lean_ctor_get(x_594, 1);
lean_inc(x_605);
lean_inc(x_604);
lean_dec(x_594);
x_606 = lean_ctor_get(x_604, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_604, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_608 = x_604;
} else {
 lean_dec_ref(x_604);
 x_608 = lean_box(0);
}
x_609 = lean_expr_update_mdata(x_5, x_606);
if (lean_is_scalar(x_608)) {
 x_610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_610 = x_608;
}
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_607);
x_611 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_611, 0, x_610);
lean_ctor_set(x_611, 1, x_605);
return x_611;
}
}
else
{
uint8_t x_612; 
lean_dec(x_5);
x_612 = !lean_is_exclusive(x_594);
if (x_612 == 0)
{
return x_594;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_594, 0);
x_614 = lean_ctor_get(x_594, 1);
lean_inc(x_614);
lean_inc(x_613);
lean_dec(x_594);
x_615 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_615, 0, x_613);
lean_ctor_set(x_615, 1, x_614);
return x_615;
}
}
}
case 11:
{
lean_object* x_616; lean_object* x_617; 
lean_free_object(x_216);
x_616 = lean_ctor_get(x_5, 2);
lean_inc(x_616);
x_617 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_616, x_6, x_437, x_8, x_434);
if (lean_obj_tag(x_617) == 0)
{
uint8_t x_618; 
x_618 = !lean_is_exclusive(x_617);
if (x_618 == 0)
{
lean_object* x_619; uint8_t x_620; 
x_619 = lean_ctor_get(x_617, 0);
x_620 = !lean_is_exclusive(x_619);
if (x_620 == 0)
{
lean_object* x_621; lean_object* x_622; 
x_621 = lean_ctor_get(x_619, 0);
x_622 = lean_expr_update_proj(x_5, x_621);
lean_ctor_set(x_619, 0, x_622);
return x_617;
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_623 = lean_ctor_get(x_619, 0);
x_624 = lean_ctor_get(x_619, 1);
lean_inc(x_624);
lean_inc(x_623);
lean_dec(x_619);
x_625 = lean_expr_update_proj(x_5, x_623);
x_626 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_626, 0, x_625);
lean_ctor_set(x_626, 1, x_624);
lean_ctor_set(x_617, 0, x_626);
return x_617;
}
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_627 = lean_ctor_get(x_617, 0);
x_628 = lean_ctor_get(x_617, 1);
lean_inc(x_628);
lean_inc(x_627);
lean_dec(x_617);
x_629 = lean_ctor_get(x_627, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_627, 1);
lean_inc(x_630);
if (lean_is_exclusive(x_627)) {
 lean_ctor_release(x_627, 0);
 lean_ctor_release(x_627, 1);
 x_631 = x_627;
} else {
 lean_dec_ref(x_627);
 x_631 = lean_box(0);
}
x_632 = lean_expr_update_proj(x_5, x_629);
if (lean_is_scalar(x_631)) {
 x_633 = lean_alloc_ctor(0, 2, 0);
} else {
 x_633 = x_631;
}
lean_ctor_set(x_633, 0, x_632);
lean_ctor_set(x_633, 1, x_630);
x_634 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_634, 0, x_633);
lean_ctor_set(x_634, 1, x_628);
return x_634;
}
}
else
{
uint8_t x_635; 
lean_dec(x_5);
x_635 = !lean_is_exclusive(x_617);
if (x_635 == 0)
{
return x_617;
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_636 = lean_ctor_get(x_617, 0);
x_637 = lean_ctor_get(x_617, 1);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_617);
x_638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_638, 0, x_636);
lean_ctor_set(x_638, 1, x_637);
return x_638;
}
}
}
default: 
{
lean_object* x_639; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_639 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_639, 0, x_5);
lean_ctor_set(x_639, 1, x_437);
lean_ctor_set(x_216, 0, x_639);
return x_216;
}
}
}
else
{
lean_object* x_640; lean_object* x_641; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_640 = l_Lean_mkBVar(x_6);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_437);
lean_ctor_set(x_216, 0, x_641);
return x_216;
}
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; uint8_t x_645; uint8_t x_646; 
x_642 = lean_ctor_get(x_216, 1);
lean_inc(x_642);
lean_dec(x_216);
x_643 = lean_unsigned_to_nat(1u);
x_644 = lean_nat_add(x_7, x_643);
x_645 = l_Lean_Occurrences_contains(x_1, x_7);
lean_dec(x_7);
x_646 = l_coeDecidableEq(x_645);
if (x_646 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_647 = lean_ctor_get(x_5, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_5, 1);
lean_inc(x_648);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_649 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_647, x_6, x_644, x_8, x_642);
if (lean_obj_tag(x_649) == 0)
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_649, 1);
lean_inc(x_651);
lean_dec(x_649);
x_652 = lean_ctor_get(x_650, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_650, 1);
lean_inc(x_653);
lean_dec(x_650);
x_654 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_648, x_6, x_653, x_8, x_651);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_655 = lean_ctor_get(x_654, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_654, 1);
lean_inc(x_656);
if (lean_is_exclusive(x_654)) {
 lean_ctor_release(x_654, 0);
 lean_ctor_release(x_654, 1);
 x_657 = x_654;
} else {
 lean_dec_ref(x_654);
 x_657 = lean_box(0);
}
x_658 = lean_ctor_get(x_655, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_655, 1);
lean_inc(x_659);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_660 = x_655;
} else {
 lean_dec_ref(x_655);
 x_660 = lean_box(0);
}
x_661 = lean_expr_update_app(x_5, x_652, x_658);
if (lean_is_scalar(x_660)) {
 x_662 = lean_alloc_ctor(0, 2, 0);
} else {
 x_662 = x_660;
}
lean_ctor_set(x_662, 0, x_661);
lean_ctor_set(x_662, 1, x_659);
if (lean_is_scalar(x_657)) {
 x_663 = lean_alloc_ctor(0, 2, 0);
} else {
 x_663 = x_657;
}
lean_ctor_set(x_663, 0, x_662);
lean_ctor_set(x_663, 1, x_656);
return x_663;
}
else
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
lean_dec(x_652);
lean_dec(x_5);
x_664 = lean_ctor_get(x_654, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_654, 1);
lean_inc(x_665);
if (lean_is_exclusive(x_654)) {
 lean_ctor_release(x_654, 0);
 lean_ctor_release(x_654, 1);
 x_666 = x_654;
} else {
 lean_dec_ref(x_654);
 x_666 = lean_box(0);
}
if (lean_is_scalar(x_666)) {
 x_667 = lean_alloc_ctor(1, 2, 0);
} else {
 x_667 = x_666;
}
lean_ctor_set(x_667, 0, x_664);
lean_ctor_set(x_667, 1, x_665);
return x_667;
}
}
else
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
lean_dec(x_648);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_668 = lean_ctor_get(x_649, 0);
lean_inc(x_668);
x_669 = lean_ctor_get(x_649, 1);
lean_inc(x_669);
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 lean_ctor_release(x_649, 1);
 x_670 = x_649;
} else {
 lean_dec_ref(x_649);
 x_670 = lean_box(0);
}
if (lean_is_scalar(x_670)) {
 x_671 = lean_alloc_ctor(1, 2, 0);
} else {
 x_671 = x_670;
}
lean_ctor_set(x_671, 0, x_668);
lean_ctor_set(x_671, 1, x_669);
return x_671;
}
}
case 6:
{
lean_object* x_672; lean_object* x_673; uint64_t x_674; lean_object* x_675; 
x_672 = lean_ctor_get(x_5, 1);
lean_inc(x_672);
x_673 = lean_ctor_get(x_5, 2);
lean_inc(x_673);
x_674 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_675 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_672, x_6, x_644, x_8, x_642);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_676 = lean_ctor_get(x_675, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_675, 1);
lean_inc(x_677);
lean_dec(x_675);
x_678 = lean_ctor_get(x_676, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_676, 1);
lean_inc(x_679);
lean_dec(x_676);
x_680 = lean_nat_add(x_6, x_643);
lean_dec(x_6);
x_681 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_673, x_680, x_679, x_8, x_677);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; uint8_t x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_682 = lean_ctor_get(x_681, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_681, 1);
lean_inc(x_683);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 lean_ctor_release(x_681, 1);
 x_684 = x_681;
} else {
 lean_dec_ref(x_681);
 x_684 = lean_box(0);
}
x_685 = lean_ctor_get(x_682, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_682, 1);
lean_inc(x_686);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_687 = x_682;
} else {
 lean_dec_ref(x_682);
 x_687 = lean_box(0);
}
x_688 = (uint8_t)((x_674 << 24) >> 61);
x_689 = lean_expr_update_lambda(x_5, x_688, x_678, x_685);
if (lean_is_scalar(x_687)) {
 x_690 = lean_alloc_ctor(0, 2, 0);
} else {
 x_690 = x_687;
}
lean_ctor_set(x_690, 0, x_689);
lean_ctor_set(x_690, 1, x_686);
if (lean_is_scalar(x_684)) {
 x_691 = lean_alloc_ctor(0, 2, 0);
} else {
 x_691 = x_684;
}
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_683);
return x_691;
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
lean_dec(x_678);
lean_dec(x_5);
x_692 = lean_ctor_get(x_681, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_681, 1);
lean_inc(x_693);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 lean_ctor_release(x_681, 1);
 x_694 = x_681;
} else {
 lean_dec_ref(x_681);
 x_694 = lean_box(0);
}
if (lean_is_scalar(x_694)) {
 x_695 = lean_alloc_ctor(1, 2, 0);
} else {
 x_695 = x_694;
}
lean_ctor_set(x_695, 0, x_692);
lean_ctor_set(x_695, 1, x_693);
return x_695;
}
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec(x_673);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_696 = lean_ctor_get(x_675, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_675, 1);
lean_inc(x_697);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 lean_ctor_release(x_675, 1);
 x_698 = x_675;
} else {
 lean_dec_ref(x_675);
 x_698 = lean_box(0);
}
if (lean_is_scalar(x_698)) {
 x_699 = lean_alloc_ctor(1, 2, 0);
} else {
 x_699 = x_698;
}
lean_ctor_set(x_699, 0, x_696);
lean_ctor_set(x_699, 1, x_697);
return x_699;
}
}
case 7:
{
lean_object* x_700; lean_object* x_701; uint64_t x_702; lean_object* x_703; 
x_700 = lean_ctor_get(x_5, 1);
lean_inc(x_700);
x_701 = lean_ctor_get(x_5, 2);
lean_inc(x_701);
x_702 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_703 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_700, x_6, x_644, x_8, x_642);
if (lean_obj_tag(x_703) == 0)
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_704 = lean_ctor_get(x_703, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_703, 1);
lean_inc(x_705);
lean_dec(x_703);
x_706 = lean_ctor_get(x_704, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_704, 1);
lean_inc(x_707);
lean_dec(x_704);
x_708 = lean_nat_add(x_6, x_643);
lean_dec(x_6);
x_709 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_701, x_708, x_707, x_8, x_705);
if (lean_obj_tag(x_709) == 0)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; uint8_t x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_709, 1);
lean_inc(x_711);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 lean_ctor_release(x_709, 1);
 x_712 = x_709;
} else {
 lean_dec_ref(x_709);
 x_712 = lean_box(0);
}
x_713 = lean_ctor_get(x_710, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_710, 1);
lean_inc(x_714);
if (lean_is_exclusive(x_710)) {
 lean_ctor_release(x_710, 0);
 lean_ctor_release(x_710, 1);
 x_715 = x_710;
} else {
 lean_dec_ref(x_710);
 x_715 = lean_box(0);
}
x_716 = (uint8_t)((x_702 << 24) >> 61);
x_717 = lean_expr_update_forall(x_5, x_716, x_706, x_713);
if (lean_is_scalar(x_715)) {
 x_718 = lean_alloc_ctor(0, 2, 0);
} else {
 x_718 = x_715;
}
lean_ctor_set(x_718, 0, x_717);
lean_ctor_set(x_718, 1, x_714);
if (lean_is_scalar(x_712)) {
 x_719 = lean_alloc_ctor(0, 2, 0);
} else {
 x_719 = x_712;
}
lean_ctor_set(x_719, 0, x_718);
lean_ctor_set(x_719, 1, x_711);
return x_719;
}
else
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
lean_dec(x_706);
lean_dec(x_5);
x_720 = lean_ctor_get(x_709, 0);
lean_inc(x_720);
x_721 = lean_ctor_get(x_709, 1);
lean_inc(x_721);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 lean_ctor_release(x_709, 1);
 x_722 = x_709;
} else {
 lean_dec_ref(x_709);
 x_722 = lean_box(0);
}
if (lean_is_scalar(x_722)) {
 x_723 = lean_alloc_ctor(1, 2, 0);
} else {
 x_723 = x_722;
}
lean_ctor_set(x_723, 0, x_720);
lean_ctor_set(x_723, 1, x_721);
return x_723;
}
}
else
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
lean_dec(x_701);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_724 = lean_ctor_get(x_703, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_703, 1);
lean_inc(x_725);
if (lean_is_exclusive(x_703)) {
 lean_ctor_release(x_703, 0);
 lean_ctor_release(x_703, 1);
 x_726 = x_703;
} else {
 lean_dec_ref(x_703);
 x_726 = lean_box(0);
}
if (lean_is_scalar(x_726)) {
 x_727 = lean_alloc_ctor(1, 2, 0);
} else {
 x_727 = x_726;
}
lean_ctor_set(x_727, 0, x_724);
lean_ctor_set(x_727, 1, x_725);
return x_727;
}
}
case 8:
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_728 = lean_ctor_get(x_5, 1);
lean_inc(x_728);
x_729 = lean_ctor_get(x_5, 2);
lean_inc(x_729);
x_730 = lean_ctor_get(x_5, 3);
lean_inc(x_730);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_731 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_728, x_6, x_644, x_8, x_642);
if (lean_obj_tag(x_731) == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_732 = lean_ctor_get(x_731, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_731, 1);
lean_inc(x_733);
lean_dec(x_731);
x_734 = lean_ctor_get(x_732, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_732, 1);
lean_inc(x_735);
lean_dec(x_732);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_736 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_729, x_6, x_735, x_8, x_733);
if (lean_obj_tag(x_736) == 0)
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_737 = lean_ctor_get(x_736, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_736, 1);
lean_inc(x_738);
lean_dec(x_736);
x_739 = lean_ctor_get(x_737, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_737, 1);
lean_inc(x_740);
lean_dec(x_737);
x_741 = lean_nat_add(x_6, x_643);
lean_dec(x_6);
x_742 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_730, x_741, x_740, x_8, x_738);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_743 = lean_ctor_get(x_742, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_742, 1);
lean_inc(x_744);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 lean_ctor_release(x_742, 1);
 x_745 = x_742;
} else {
 lean_dec_ref(x_742);
 x_745 = lean_box(0);
}
x_746 = lean_ctor_get(x_743, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_743, 1);
lean_inc(x_747);
if (lean_is_exclusive(x_743)) {
 lean_ctor_release(x_743, 0);
 lean_ctor_release(x_743, 1);
 x_748 = x_743;
} else {
 lean_dec_ref(x_743);
 x_748 = lean_box(0);
}
x_749 = lean_expr_update_let(x_5, x_734, x_739, x_746);
if (lean_is_scalar(x_748)) {
 x_750 = lean_alloc_ctor(0, 2, 0);
} else {
 x_750 = x_748;
}
lean_ctor_set(x_750, 0, x_749);
lean_ctor_set(x_750, 1, x_747);
if (lean_is_scalar(x_745)) {
 x_751 = lean_alloc_ctor(0, 2, 0);
} else {
 x_751 = x_745;
}
lean_ctor_set(x_751, 0, x_750);
lean_ctor_set(x_751, 1, x_744);
return x_751;
}
else
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
lean_dec(x_739);
lean_dec(x_734);
lean_dec(x_5);
x_752 = lean_ctor_get(x_742, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_742, 1);
lean_inc(x_753);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 lean_ctor_release(x_742, 1);
 x_754 = x_742;
} else {
 lean_dec_ref(x_742);
 x_754 = lean_box(0);
}
if (lean_is_scalar(x_754)) {
 x_755 = lean_alloc_ctor(1, 2, 0);
} else {
 x_755 = x_754;
}
lean_ctor_set(x_755, 0, x_752);
lean_ctor_set(x_755, 1, x_753);
return x_755;
}
}
else
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; 
lean_dec(x_734);
lean_dec(x_730);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_756 = lean_ctor_get(x_736, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_736, 1);
lean_inc(x_757);
if (lean_is_exclusive(x_736)) {
 lean_ctor_release(x_736, 0);
 lean_ctor_release(x_736, 1);
 x_758 = x_736;
} else {
 lean_dec_ref(x_736);
 x_758 = lean_box(0);
}
if (lean_is_scalar(x_758)) {
 x_759 = lean_alloc_ctor(1, 2, 0);
} else {
 x_759 = x_758;
}
lean_ctor_set(x_759, 0, x_756);
lean_ctor_set(x_759, 1, x_757);
return x_759;
}
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; 
lean_dec(x_730);
lean_dec(x_729);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_760 = lean_ctor_get(x_731, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_731, 1);
lean_inc(x_761);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_762 = x_731;
} else {
 lean_dec_ref(x_731);
 x_762 = lean_box(0);
}
if (lean_is_scalar(x_762)) {
 x_763 = lean_alloc_ctor(1, 2, 0);
} else {
 x_763 = x_762;
}
lean_ctor_set(x_763, 0, x_760);
lean_ctor_set(x_763, 1, x_761);
return x_763;
}
}
case 10:
{
lean_object* x_764; lean_object* x_765; 
x_764 = lean_ctor_get(x_5, 1);
lean_inc(x_764);
x_765 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_764, x_6, x_644, x_8, x_642);
if (lean_obj_tag(x_765) == 0)
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_766 = lean_ctor_get(x_765, 0);
lean_inc(x_766);
x_767 = lean_ctor_get(x_765, 1);
lean_inc(x_767);
if (lean_is_exclusive(x_765)) {
 lean_ctor_release(x_765, 0);
 lean_ctor_release(x_765, 1);
 x_768 = x_765;
} else {
 lean_dec_ref(x_765);
 x_768 = lean_box(0);
}
x_769 = lean_ctor_get(x_766, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_766, 1);
lean_inc(x_770);
if (lean_is_exclusive(x_766)) {
 lean_ctor_release(x_766, 0);
 lean_ctor_release(x_766, 1);
 x_771 = x_766;
} else {
 lean_dec_ref(x_766);
 x_771 = lean_box(0);
}
x_772 = lean_expr_update_mdata(x_5, x_769);
if (lean_is_scalar(x_771)) {
 x_773 = lean_alloc_ctor(0, 2, 0);
} else {
 x_773 = x_771;
}
lean_ctor_set(x_773, 0, x_772);
lean_ctor_set(x_773, 1, x_770);
if (lean_is_scalar(x_768)) {
 x_774 = lean_alloc_ctor(0, 2, 0);
} else {
 x_774 = x_768;
}
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_767);
return x_774;
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
lean_dec(x_5);
x_775 = lean_ctor_get(x_765, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_765, 1);
lean_inc(x_776);
if (lean_is_exclusive(x_765)) {
 lean_ctor_release(x_765, 0);
 lean_ctor_release(x_765, 1);
 x_777 = x_765;
} else {
 lean_dec_ref(x_765);
 x_777 = lean_box(0);
}
if (lean_is_scalar(x_777)) {
 x_778 = lean_alloc_ctor(1, 2, 0);
} else {
 x_778 = x_777;
}
lean_ctor_set(x_778, 0, x_775);
lean_ctor_set(x_778, 1, x_776);
return x_778;
}
}
case 11:
{
lean_object* x_779; lean_object* x_780; 
x_779 = lean_ctor_get(x_5, 2);
lean_inc(x_779);
x_780 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_779, x_6, x_644, x_8, x_642);
if (lean_obj_tag(x_780) == 0)
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 lean_ctor_release(x_780, 1);
 x_783 = x_780;
} else {
 lean_dec_ref(x_780);
 x_783 = lean_box(0);
}
x_784 = lean_ctor_get(x_781, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_781, 1);
lean_inc(x_785);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 lean_ctor_release(x_781, 1);
 x_786 = x_781;
} else {
 lean_dec_ref(x_781);
 x_786 = lean_box(0);
}
x_787 = lean_expr_update_proj(x_5, x_784);
if (lean_is_scalar(x_786)) {
 x_788 = lean_alloc_ctor(0, 2, 0);
} else {
 x_788 = x_786;
}
lean_ctor_set(x_788, 0, x_787);
lean_ctor_set(x_788, 1, x_785);
if (lean_is_scalar(x_783)) {
 x_789 = lean_alloc_ctor(0, 2, 0);
} else {
 x_789 = x_783;
}
lean_ctor_set(x_789, 0, x_788);
lean_ctor_set(x_789, 1, x_782);
return x_789;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
lean_dec(x_5);
x_790 = lean_ctor_get(x_780, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_780, 1);
lean_inc(x_791);
if (lean_is_exclusive(x_780)) {
 lean_ctor_release(x_780, 0);
 lean_ctor_release(x_780, 1);
 x_792 = x_780;
} else {
 lean_dec_ref(x_780);
 x_792 = lean_box(0);
}
if (lean_is_scalar(x_792)) {
 x_793 = lean_alloc_ctor(1, 2, 0);
} else {
 x_793 = x_792;
}
lean_ctor_set(x_793, 0, x_790);
lean_ctor_set(x_793, 1, x_791);
return x_793;
}
}
default: 
{
lean_object* x_794; lean_object* x_795; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_794 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_794, 0, x_5);
lean_ctor_set(x_794, 1, x_644);
x_795 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_642);
return x_795;
}
}
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_796 = l_Lean_mkBVar(x_6);
x_797 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_797, 0, x_796);
lean_ctor_set(x_797, 1, x_644);
x_798 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_798, 0, x_797);
lean_ctor_set(x_798, 1, x_642);
return x_798;
}
}
}
}
else
{
uint8_t x_799; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_799 = !lean_is_exclusive(x_216);
if (x_799 == 0)
{
return x_216;
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; 
x_800 = lean_ctor_get(x_216, 0);
x_801 = lean_ctor_get(x_216, 1);
lean_inc(x_801);
lean_inc(x_800);
lean_dec(x_216);
x_802 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_802, 0, x_800);
lean_ctor_set(x_802, 1, x_801);
return x_802;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Meta_kabstract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Expr_toHeadIndex___main(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Init_Lean_HeadIndex_1__headNumArgsAux___main(x_2, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_3, x_2, x_6, x_8, x_1, x_7, x_9, x_4, x_5);
lean_dec(x_8);
lean_dec(x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Meta_kabstract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_kabstract(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Init_Lean_Data_Occurrences(lean_object*);
lean_object* initialize_Init_Lean_HeadIndex(lean_object*);
lean_object* initialize_Init_Lean_Meta_ExprDefEq(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_KAbstract(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Data_Occurrences(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_HeadIndex(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_ExprDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
