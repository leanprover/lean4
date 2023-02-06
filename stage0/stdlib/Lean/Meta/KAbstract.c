// Lean compiler output
// Module: Lean.Meta.KAbstract
// Imports: Init Lean.Data.Occurrences Lean.HeadIndex Lean.Meta.Basic
#include <lean/lean.h>
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_headNumArgs_go(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_67_(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_kabstract___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_32_(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_924; 
x_924 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_924 == 0)
{
lean_object* x_925; uint8_t x_926; 
lean_inc(x_5);
x_925 = l_Lean_Expr_toHeadIndex(x_5);
x_926 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_67_(x_925, x_3);
lean_dec(x_925);
if (x_926 == 0)
{
uint8_t x_927; 
x_927 = 1;
x_13 = x_927;
goto block_923;
}
else
{
lean_object* x_928; lean_object* x_929; uint8_t x_930; 
x_928 = lean_unsigned_to_nat(0u);
x_929 = l_Lean_Expr_headNumArgs_go(x_5, x_928);
x_930 = lean_nat_dec_eq(x_929, x_4);
lean_dec(x_929);
if (x_930 == 0)
{
uint8_t x_931; 
x_931 = 1;
x_13 = x_931;
goto block_923;
}
else
{
uint8_t x_932; 
x_932 = 0;
x_13 = x_932;
goto block_923;
}
}
}
else
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_933 = lean_ctor_get(x_5, 0);
lean_inc(x_933);
x_934 = lean_ctor_get(x_5, 1);
lean_inc(x_934);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_933);
lean_inc(x_1);
x_935 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_933, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_935) == 0)
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_936 = lean_ctor_get(x_935, 0);
lean_inc(x_936);
x_937 = lean_ctor_get(x_935, 1);
lean_inc(x_937);
lean_dec(x_935);
lean_inc(x_934);
x_938 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_934, x_6, x_7, x_8, x_9, x_10, x_11, x_937);
if (lean_obj_tag(x_938) == 0)
{
uint8_t x_939; 
x_939 = !lean_is_exclusive(x_938);
if (x_939 == 0)
{
lean_object* x_940; size_t x_941; size_t x_942; uint8_t x_943; 
x_940 = lean_ctor_get(x_938, 0);
x_941 = lean_ptr_addr(x_933);
lean_dec(x_933);
x_942 = lean_ptr_addr(x_936);
x_943 = lean_usize_dec_eq(x_941, x_942);
if (x_943 == 0)
{
lean_object* x_944; 
lean_dec(x_934);
lean_dec(x_5);
x_944 = l_Lean_Expr_app___override(x_936, x_940);
lean_ctor_set(x_938, 0, x_944);
return x_938;
}
else
{
size_t x_945; size_t x_946; uint8_t x_947; 
x_945 = lean_ptr_addr(x_934);
lean_dec(x_934);
x_946 = lean_ptr_addr(x_940);
x_947 = lean_usize_dec_eq(x_945, x_946);
if (x_947 == 0)
{
lean_object* x_948; 
lean_dec(x_5);
x_948 = l_Lean_Expr_app___override(x_936, x_940);
lean_ctor_set(x_938, 0, x_948);
return x_938;
}
else
{
lean_dec(x_940);
lean_dec(x_936);
lean_ctor_set(x_938, 0, x_5);
return x_938;
}
}
}
else
{
lean_object* x_949; lean_object* x_950; size_t x_951; size_t x_952; uint8_t x_953; 
x_949 = lean_ctor_get(x_938, 0);
x_950 = lean_ctor_get(x_938, 1);
lean_inc(x_950);
lean_inc(x_949);
lean_dec(x_938);
x_951 = lean_ptr_addr(x_933);
lean_dec(x_933);
x_952 = lean_ptr_addr(x_936);
x_953 = lean_usize_dec_eq(x_951, x_952);
if (x_953 == 0)
{
lean_object* x_954; lean_object* x_955; 
lean_dec(x_934);
lean_dec(x_5);
x_954 = l_Lean_Expr_app___override(x_936, x_949);
x_955 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_955, 0, x_954);
lean_ctor_set(x_955, 1, x_950);
return x_955;
}
else
{
size_t x_956; size_t x_957; uint8_t x_958; 
x_956 = lean_ptr_addr(x_934);
lean_dec(x_934);
x_957 = lean_ptr_addr(x_949);
x_958 = lean_usize_dec_eq(x_956, x_957);
if (x_958 == 0)
{
lean_object* x_959; lean_object* x_960; 
lean_dec(x_5);
x_959 = l_Lean_Expr_app___override(x_936, x_949);
x_960 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_960, 0, x_959);
lean_ctor_set(x_960, 1, x_950);
return x_960;
}
else
{
lean_object* x_961; 
lean_dec(x_949);
lean_dec(x_936);
x_961 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_961, 0, x_5);
lean_ctor_set(x_961, 1, x_950);
return x_961;
}
}
}
}
else
{
uint8_t x_962; 
lean_dec(x_936);
lean_dec(x_934);
lean_dec(x_933);
lean_dec(x_5);
x_962 = !lean_is_exclusive(x_938);
if (x_962 == 0)
{
return x_938;
}
else
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; 
x_963 = lean_ctor_get(x_938, 0);
x_964 = lean_ctor_get(x_938, 1);
lean_inc(x_964);
lean_inc(x_963);
lean_dec(x_938);
x_965 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_965, 0, x_963);
lean_ctor_set(x_965, 1, x_964);
return x_965;
}
}
}
else
{
uint8_t x_966; 
lean_dec(x_934);
lean_dec(x_933);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_966 = !lean_is_exclusive(x_935);
if (x_966 == 0)
{
return x_935;
}
else
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; 
x_967 = lean_ctor_get(x_935, 0);
x_968 = lean_ctor_get(x_935, 1);
lean_inc(x_968);
lean_inc(x_967);
lean_dec(x_935);
x_969 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_969, 0, x_967);
lean_ctor_set(x_969, 1, x_968);
return x_969;
}
}
}
case 6:
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; uint8_t x_973; lean_object* x_974; 
x_970 = lean_ctor_get(x_5, 0);
lean_inc(x_970);
x_971 = lean_ctor_get(x_5, 1);
lean_inc(x_971);
x_972 = lean_ctor_get(x_5, 2);
lean_inc(x_972);
x_973 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_971);
lean_inc(x_1);
x_974 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_971, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_974) == 0)
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; 
x_975 = lean_ctor_get(x_974, 0);
lean_inc(x_975);
x_976 = lean_ctor_get(x_974, 1);
lean_inc(x_976);
lean_dec(x_974);
x_977 = lean_unsigned_to_nat(1u);
x_978 = lean_nat_add(x_6, x_977);
lean_dec(x_6);
lean_inc(x_972);
x_979 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_972, x_978, x_7, x_8, x_9, x_10, x_11, x_976);
if (lean_obj_tag(x_979) == 0)
{
uint8_t x_980; 
x_980 = !lean_is_exclusive(x_979);
if (x_980 == 0)
{
lean_object* x_981; lean_object* x_982; size_t x_983; size_t x_984; uint8_t x_985; 
x_981 = lean_ctor_get(x_979, 0);
lean_inc(x_972);
lean_inc(x_971);
lean_inc(x_970);
x_982 = l_Lean_Expr_lam___override(x_970, x_971, x_972, x_973);
x_983 = lean_ptr_addr(x_971);
lean_dec(x_971);
x_984 = lean_ptr_addr(x_975);
x_985 = lean_usize_dec_eq(x_983, x_984);
if (x_985 == 0)
{
lean_object* x_986; 
lean_dec(x_982);
lean_dec(x_972);
x_986 = l_Lean_Expr_lam___override(x_970, x_975, x_981, x_973);
lean_ctor_set(x_979, 0, x_986);
return x_979;
}
else
{
size_t x_987; size_t x_988; uint8_t x_989; 
x_987 = lean_ptr_addr(x_972);
lean_dec(x_972);
x_988 = lean_ptr_addr(x_981);
x_989 = lean_usize_dec_eq(x_987, x_988);
if (x_989 == 0)
{
lean_object* x_990; 
lean_dec(x_982);
x_990 = l_Lean_Expr_lam___override(x_970, x_975, x_981, x_973);
lean_ctor_set(x_979, 0, x_990);
return x_979;
}
else
{
uint8_t x_991; 
x_991 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_973, x_973);
if (x_991 == 0)
{
lean_object* x_992; 
lean_dec(x_982);
x_992 = l_Lean_Expr_lam___override(x_970, x_975, x_981, x_973);
lean_ctor_set(x_979, 0, x_992);
return x_979;
}
else
{
lean_dec(x_981);
lean_dec(x_975);
lean_dec(x_970);
lean_ctor_set(x_979, 0, x_982);
return x_979;
}
}
}
}
else
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; size_t x_996; size_t x_997; uint8_t x_998; 
x_993 = lean_ctor_get(x_979, 0);
x_994 = lean_ctor_get(x_979, 1);
lean_inc(x_994);
lean_inc(x_993);
lean_dec(x_979);
lean_inc(x_972);
lean_inc(x_971);
lean_inc(x_970);
x_995 = l_Lean_Expr_lam___override(x_970, x_971, x_972, x_973);
x_996 = lean_ptr_addr(x_971);
lean_dec(x_971);
x_997 = lean_ptr_addr(x_975);
x_998 = lean_usize_dec_eq(x_996, x_997);
if (x_998 == 0)
{
lean_object* x_999; lean_object* x_1000; 
lean_dec(x_995);
lean_dec(x_972);
x_999 = l_Lean_Expr_lam___override(x_970, x_975, x_993, x_973);
x_1000 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1000, 0, x_999);
lean_ctor_set(x_1000, 1, x_994);
return x_1000;
}
else
{
size_t x_1001; size_t x_1002; uint8_t x_1003; 
x_1001 = lean_ptr_addr(x_972);
lean_dec(x_972);
x_1002 = lean_ptr_addr(x_993);
x_1003 = lean_usize_dec_eq(x_1001, x_1002);
if (x_1003 == 0)
{
lean_object* x_1004; lean_object* x_1005; 
lean_dec(x_995);
x_1004 = l_Lean_Expr_lam___override(x_970, x_975, x_993, x_973);
x_1005 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1005, 0, x_1004);
lean_ctor_set(x_1005, 1, x_994);
return x_1005;
}
else
{
uint8_t x_1006; 
x_1006 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_973, x_973);
if (x_1006 == 0)
{
lean_object* x_1007; lean_object* x_1008; 
lean_dec(x_995);
x_1007 = l_Lean_Expr_lam___override(x_970, x_975, x_993, x_973);
x_1008 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1008, 0, x_1007);
lean_ctor_set(x_1008, 1, x_994);
return x_1008;
}
else
{
lean_object* x_1009; 
lean_dec(x_993);
lean_dec(x_975);
lean_dec(x_970);
x_1009 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1009, 0, x_995);
lean_ctor_set(x_1009, 1, x_994);
return x_1009;
}
}
}
}
}
else
{
uint8_t x_1010; 
lean_dec(x_975);
lean_dec(x_972);
lean_dec(x_971);
lean_dec(x_970);
x_1010 = !lean_is_exclusive(x_979);
if (x_1010 == 0)
{
return x_979;
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_1011 = lean_ctor_get(x_979, 0);
x_1012 = lean_ctor_get(x_979, 1);
lean_inc(x_1012);
lean_inc(x_1011);
lean_dec(x_979);
x_1013 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1013, 0, x_1011);
lean_ctor_set(x_1013, 1, x_1012);
return x_1013;
}
}
}
else
{
uint8_t x_1014; 
lean_dec(x_972);
lean_dec(x_971);
lean_dec(x_970);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1014 = !lean_is_exclusive(x_974);
if (x_1014 == 0)
{
return x_974;
}
else
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
x_1015 = lean_ctor_get(x_974, 0);
x_1016 = lean_ctor_get(x_974, 1);
lean_inc(x_1016);
lean_inc(x_1015);
lean_dec(x_974);
x_1017 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1017, 0, x_1015);
lean_ctor_set(x_1017, 1, x_1016);
return x_1017;
}
}
}
case 7:
{
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; uint8_t x_1021; lean_object* x_1022; 
x_1018 = lean_ctor_get(x_5, 0);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_5, 1);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_5, 2);
lean_inc(x_1020);
x_1021 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1019);
lean_inc(x_1);
x_1022 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1019, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1022) == 0)
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; 
x_1023 = lean_ctor_get(x_1022, 0);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_1022, 1);
lean_inc(x_1024);
lean_dec(x_1022);
x_1025 = lean_unsigned_to_nat(1u);
x_1026 = lean_nat_add(x_6, x_1025);
lean_dec(x_6);
lean_inc(x_1020);
x_1027 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1020, x_1026, x_7, x_8, x_9, x_10, x_11, x_1024);
if (lean_obj_tag(x_1027) == 0)
{
uint8_t x_1028; 
x_1028 = !lean_is_exclusive(x_1027);
if (x_1028 == 0)
{
lean_object* x_1029; lean_object* x_1030; size_t x_1031; size_t x_1032; uint8_t x_1033; 
x_1029 = lean_ctor_get(x_1027, 0);
lean_inc(x_1020);
lean_inc(x_1019);
lean_inc(x_1018);
x_1030 = l_Lean_Expr_forallE___override(x_1018, x_1019, x_1020, x_1021);
x_1031 = lean_ptr_addr(x_1019);
lean_dec(x_1019);
x_1032 = lean_ptr_addr(x_1023);
x_1033 = lean_usize_dec_eq(x_1031, x_1032);
if (x_1033 == 0)
{
lean_object* x_1034; 
lean_dec(x_1030);
lean_dec(x_1020);
x_1034 = l_Lean_Expr_forallE___override(x_1018, x_1023, x_1029, x_1021);
lean_ctor_set(x_1027, 0, x_1034);
return x_1027;
}
else
{
size_t x_1035; size_t x_1036; uint8_t x_1037; 
x_1035 = lean_ptr_addr(x_1020);
lean_dec(x_1020);
x_1036 = lean_ptr_addr(x_1029);
x_1037 = lean_usize_dec_eq(x_1035, x_1036);
if (x_1037 == 0)
{
lean_object* x_1038; 
lean_dec(x_1030);
x_1038 = l_Lean_Expr_forallE___override(x_1018, x_1023, x_1029, x_1021);
lean_ctor_set(x_1027, 0, x_1038);
return x_1027;
}
else
{
uint8_t x_1039; 
x_1039 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_1021, x_1021);
if (x_1039 == 0)
{
lean_object* x_1040; 
lean_dec(x_1030);
x_1040 = l_Lean_Expr_forallE___override(x_1018, x_1023, x_1029, x_1021);
lean_ctor_set(x_1027, 0, x_1040);
return x_1027;
}
else
{
lean_dec(x_1029);
lean_dec(x_1023);
lean_dec(x_1018);
lean_ctor_set(x_1027, 0, x_1030);
return x_1027;
}
}
}
}
else
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; size_t x_1044; size_t x_1045; uint8_t x_1046; 
x_1041 = lean_ctor_get(x_1027, 0);
x_1042 = lean_ctor_get(x_1027, 1);
lean_inc(x_1042);
lean_inc(x_1041);
lean_dec(x_1027);
lean_inc(x_1020);
lean_inc(x_1019);
lean_inc(x_1018);
x_1043 = l_Lean_Expr_forallE___override(x_1018, x_1019, x_1020, x_1021);
x_1044 = lean_ptr_addr(x_1019);
lean_dec(x_1019);
x_1045 = lean_ptr_addr(x_1023);
x_1046 = lean_usize_dec_eq(x_1044, x_1045);
if (x_1046 == 0)
{
lean_object* x_1047; lean_object* x_1048; 
lean_dec(x_1043);
lean_dec(x_1020);
x_1047 = l_Lean_Expr_forallE___override(x_1018, x_1023, x_1041, x_1021);
x_1048 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1048, 0, x_1047);
lean_ctor_set(x_1048, 1, x_1042);
return x_1048;
}
else
{
size_t x_1049; size_t x_1050; uint8_t x_1051; 
x_1049 = lean_ptr_addr(x_1020);
lean_dec(x_1020);
x_1050 = lean_ptr_addr(x_1041);
x_1051 = lean_usize_dec_eq(x_1049, x_1050);
if (x_1051 == 0)
{
lean_object* x_1052; lean_object* x_1053; 
lean_dec(x_1043);
x_1052 = l_Lean_Expr_forallE___override(x_1018, x_1023, x_1041, x_1021);
x_1053 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1053, 0, x_1052);
lean_ctor_set(x_1053, 1, x_1042);
return x_1053;
}
else
{
uint8_t x_1054; 
x_1054 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_1021, x_1021);
if (x_1054 == 0)
{
lean_object* x_1055; lean_object* x_1056; 
lean_dec(x_1043);
x_1055 = l_Lean_Expr_forallE___override(x_1018, x_1023, x_1041, x_1021);
x_1056 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1056, 0, x_1055);
lean_ctor_set(x_1056, 1, x_1042);
return x_1056;
}
else
{
lean_object* x_1057; 
lean_dec(x_1041);
lean_dec(x_1023);
lean_dec(x_1018);
x_1057 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1057, 0, x_1043);
lean_ctor_set(x_1057, 1, x_1042);
return x_1057;
}
}
}
}
}
else
{
uint8_t x_1058; 
lean_dec(x_1023);
lean_dec(x_1020);
lean_dec(x_1019);
lean_dec(x_1018);
x_1058 = !lean_is_exclusive(x_1027);
if (x_1058 == 0)
{
return x_1027;
}
else
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; 
x_1059 = lean_ctor_get(x_1027, 0);
x_1060 = lean_ctor_get(x_1027, 1);
lean_inc(x_1060);
lean_inc(x_1059);
lean_dec(x_1027);
x_1061 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1061, 0, x_1059);
lean_ctor_set(x_1061, 1, x_1060);
return x_1061;
}
}
}
else
{
uint8_t x_1062; 
lean_dec(x_1020);
lean_dec(x_1019);
lean_dec(x_1018);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1062 = !lean_is_exclusive(x_1022);
if (x_1062 == 0)
{
return x_1022;
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
x_1063 = lean_ctor_get(x_1022, 0);
x_1064 = lean_ctor_get(x_1022, 1);
lean_inc(x_1064);
lean_inc(x_1063);
lean_dec(x_1022);
x_1065 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1065, 0, x_1063);
lean_ctor_set(x_1065, 1, x_1064);
return x_1065;
}
}
}
case 8:
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; uint8_t x_1070; lean_object* x_1071; 
x_1066 = lean_ctor_get(x_5, 0);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_5, 1);
lean_inc(x_1067);
x_1068 = lean_ctor_get(x_5, 2);
lean_inc(x_1068);
x_1069 = lean_ctor_get(x_5, 3);
lean_inc(x_1069);
x_1070 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1067);
lean_inc(x_1);
x_1071 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1067, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1071) == 0)
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
x_1072 = lean_ctor_get(x_1071, 0);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_1071, 1);
lean_inc(x_1073);
lean_dec(x_1071);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1068);
lean_inc(x_1);
x_1074 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1068, x_6, x_7, x_8, x_9, x_10, x_11, x_1073);
if (lean_obj_tag(x_1074) == 0)
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1075 = lean_ctor_get(x_1074, 0);
lean_inc(x_1075);
x_1076 = lean_ctor_get(x_1074, 1);
lean_inc(x_1076);
lean_dec(x_1074);
x_1077 = lean_unsigned_to_nat(1u);
x_1078 = lean_nat_add(x_6, x_1077);
lean_dec(x_6);
lean_inc(x_1069);
x_1079 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1069, x_1078, x_7, x_8, x_9, x_10, x_11, x_1076);
if (lean_obj_tag(x_1079) == 0)
{
uint8_t x_1080; 
x_1080 = !lean_is_exclusive(x_1079);
if (x_1080 == 0)
{
lean_object* x_1081; size_t x_1082; size_t x_1083; uint8_t x_1084; 
x_1081 = lean_ctor_get(x_1079, 0);
x_1082 = lean_ptr_addr(x_1067);
lean_dec(x_1067);
x_1083 = lean_ptr_addr(x_1072);
x_1084 = lean_usize_dec_eq(x_1082, x_1083);
if (x_1084 == 0)
{
lean_object* x_1085; 
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_5);
x_1085 = l_Lean_Expr_letE___override(x_1066, x_1072, x_1075, x_1081, x_1070);
lean_ctor_set(x_1079, 0, x_1085);
return x_1079;
}
else
{
size_t x_1086; size_t x_1087; uint8_t x_1088; 
x_1086 = lean_ptr_addr(x_1068);
lean_dec(x_1068);
x_1087 = lean_ptr_addr(x_1075);
x_1088 = lean_usize_dec_eq(x_1086, x_1087);
if (x_1088 == 0)
{
lean_object* x_1089; 
lean_dec(x_1069);
lean_dec(x_5);
x_1089 = l_Lean_Expr_letE___override(x_1066, x_1072, x_1075, x_1081, x_1070);
lean_ctor_set(x_1079, 0, x_1089);
return x_1079;
}
else
{
size_t x_1090; size_t x_1091; uint8_t x_1092; 
x_1090 = lean_ptr_addr(x_1069);
lean_dec(x_1069);
x_1091 = lean_ptr_addr(x_1081);
x_1092 = lean_usize_dec_eq(x_1090, x_1091);
if (x_1092 == 0)
{
lean_object* x_1093; 
lean_dec(x_5);
x_1093 = l_Lean_Expr_letE___override(x_1066, x_1072, x_1075, x_1081, x_1070);
lean_ctor_set(x_1079, 0, x_1093);
return x_1079;
}
else
{
lean_dec(x_1081);
lean_dec(x_1075);
lean_dec(x_1072);
lean_dec(x_1066);
lean_ctor_set(x_1079, 0, x_5);
return x_1079;
}
}
}
}
else
{
lean_object* x_1094; lean_object* x_1095; size_t x_1096; size_t x_1097; uint8_t x_1098; 
x_1094 = lean_ctor_get(x_1079, 0);
x_1095 = lean_ctor_get(x_1079, 1);
lean_inc(x_1095);
lean_inc(x_1094);
lean_dec(x_1079);
x_1096 = lean_ptr_addr(x_1067);
lean_dec(x_1067);
x_1097 = lean_ptr_addr(x_1072);
x_1098 = lean_usize_dec_eq(x_1096, x_1097);
if (x_1098 == 0)
{
lean_object* x_1099; lean_object* x_1100; 
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_5);
x_1099 = l_Lean_Expr_letE___override(x_1066, x_1072, x_1075, x_1094, x_1070);
x_1100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1100, 0, x_1099);
lean_ctor_set(x_1100, 1, x_1095);
return x_1100;
}
else
{
size_t x_1101; size_t x_1102; uint8_t x_1103; 
x_1101 = lean_ptr_addr(x_1068);
lean_dec(x_1068);
x_1102 = lean_ptr_addr(x_1075);
x_1103 = lean_usize_dec_eq(x_1101, x_1102);
if (x_1103 == 0)
{
lean_object* x_1104; lean_object* x_1105; 
lean_dec(x_1069);
lean_dec(x_5);
x_1104 = l_Lean_Expr_letE___override(x_1066, x_1072, x_1075, x_1094, x_1070);
x_1105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1105, 0, x_1104);
lean_ctor_set(x_1105, 1, x_1095);
return x_1105;
}
else
{
size_t x_1106; size_t x_1107; uint8_t x_1108; 
x_1106 = lean_ptr_addr(x_1069);
lean_dec(x_1069);
x_1107 = lean_ptr_addr(x_1094);
x_1108 = lean_usize_dec_eq(x_1106, x_1107);
if (x_1108 == 0)
{
lean_object* x_1109; lean_object* x_1110; 
lean_dec(x_5);
x_1109 = l_Lean_Expr_letE___override(x_1066, x_1072, x_1075, x_1094, x_1070);
x_1110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1110, 0, x_1109);
lean_ctor_set(x_1110, 1, x_1095);
return x_1110;
}
else
{
lean_object* x_1111; 
lean_dec(x_1094);
lean_dec(x_1075);
lean_dec(x_1072);
lean_dec(x_1066);
x_1111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1111, 0, x_5);
lean_ctor_set(x_1111, 1, x_1095);
return x_1111;
}
}
}
}
}
else
{
uint8_t x_1112; 
lean_dec(x_1075);
lean_dec(x_1072);
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_1067);
lean_dec(x_1066);
lean_dec(x_5);
x_1112 = !lean_is_exclusive(x_1079);
if (x_1112 == 0)
{
return x_1079;
}
else
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
x_1113 = lean_ctor_get(x_1079, 0);
x_1114 = lean_ctor_get(x_1079, 1);
lean_inc(x_1114);
lean_inc(x_1113);
lean_dec(x_1079);
x_1115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1115, 0, x_1113);
lean_ctor_set(x_1115, 1, x_1114);
return x_1115;
}
}
}
else
{
uint8_t x_1116; 
lean_dec(x_1072);
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_1067);
lean_dec(x_1066);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1116 = !lean_is_exclusive(x_1074);
if (x_1116 == 0)
{
return x_1074;
}
else
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; 
x_1117 = lean_ctor_get(x_1074, 0);
x_1118 = lean_ctor_get(x_1074, 1);
lean_inc(x_1118);
lean_inc(x_1117);
lean_dec(x_1074);
x_1119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1119, 0, x_1117);
lean_ctor_set(x_1119, 1, x_1118);
return x_1119;
}
}
}
else
{
uint8_t x_1120; 
lean_dec(x_1069);
lean_dec(x_1068);
lean_dec(x_1067);
lean_dec(x_1066);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1120 = !lean_is_exclusive(x_1071);
if (x_1120 == 0)
{
return x_1071;
}
else
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
x_1121 = lean_ctor_get(x_1071, 0);
x_1122 = lean_ctor_get(x_1071, 1);
lean_inc(x_1122);
lean_inc(x_1121);
lean_dec(x_1071);
x_1123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1123, 0, x_1121);
lean_ctor_set(x_1123, 1, x_1122);
return x_1123;
}
}
}
case 10:
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
x_1124 = lean_ctor_get(x_5, 0);
lean_inc(x_1124);
x_1125 = lean_ctor_get(x_5, 1);
lean_inc(x_1125);
lean_inc(x_1125);
x_1126 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1125, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1126) == 0)
{
uint8_t x_1127; 
x_1127 = !lean_is_exclusive(x_1126);
if (x_1127 == 0)
{
lean_object* x_1128; size_t x_1129; size_t x_1130; uint8_t x_1131; 
x_1128 = lean_ctor_get(x_1126, 0);
x_1129 = lean_ptr_addr(x_1125);
lean_dec(x_1125);
x_1130 = lean_ptr_addr(x_1128);
x_1131 = lean_usize_dec_eq(x_1129, x_1130);
if (x_1131 == 0)
{
lean_object* x_1132; 
lean_dec(x_5);
x_1132 = l_Lean_Expr_mdata___override(x_1124, x_1128);
lean_ctor_set(x_1126, 0, x_1132);
return x_1126;
}
else
{
lean_dec(x_1128);
lean_dec(x_1124);
lean_ctor_set(x_1126, 0, x_5);
return x_1126;
}
}
else
{
lean_object* x_1133; lean_object* x_1134; size_t x_1135; size_t x_1136; uint8_t x_1137; 
x_1133 = lean_ctor_get(x_1126, 0);
x_1134 = lean_ctor_get(x_1126, 1);
lean_inc(x_1134);
lean_inc(x_1133);
lean_dec(x_1126);
x_1135 = lean_ptr_addr(x_1125);
lean_dec(x_1125);
x_1136 = lean_ptr_addr(x_1133);
x_1137 = lean_usize_dec_eq(x_1135, x_1136);
if (x_1137 == 0)
{
lean_object* x_1138; lean_object* x_1139; 
lean_dec(x_5);
x_1138 = l_Lean_Expr_mdata___override(x_1124, x_1133);
x_1139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1139, 0, x_1138);
lean_ctor_set(x_1139, 1, x_1134);
return x_1139;
}
else
{
lean_object* x_1140; 
lean_dec(x_1133);
lean_dec(x_1124);
x_1140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1140, 0, x_5);
lean_ctor_set(x_1140, 1, x_1134);
return x_1140;
}
}
}
else
{
uint8_t x_1141; 
lean_dec(x_1125);
lean_dec(x_1124);
lean_dec(x_5);
x_1141 = !lean_is_exclusive(x_1126);
if (x_1141 == 0)
{
return x_1126;
}
else
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
x_1142 = lean_ctor_get(x_1126, 0);
x_1143 = lean_ctor_get(x_1126, 1);
lean_inc(x_1143);
lean_inc(x_1142);
lean_dec(x_1126);
x_1144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1144, 0, x_1142);
lean_ctor_set(x_1144, 1, x_1143);
return x_1144;
}
}
}
case 11:
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; 
x_1145 = lean_ctor_get(x_5, 0);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_5, 1);
lean_inc(x_1146);
x_1147 = lean_ctor_get(x_5, 2);
lean_inc(x_1147);
lean_inc(x_1147);
x_1148 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1147, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1148) == 0)
{
uint8_t x_1149; 
x_1149 = !lean_is_exclusive(x_1148);
if (x_1149 == 0)
{
lean_object* x_1150; size_t x_1151; size_t x_1152; uint8_t x_1153; 
x_1150 = lean_ctor_get(x_1148, 0);
x_1151 = lean_ptr_addr(x_1147);
lean_dec(x_1147);
x_1152 = lean_ptr_addr(x_1150);
x_1153 = lean_usize_dec_eq(x_1151, x_1152);
if (x_1153 == 0)
{
lean_object* x_1154; 
lean_dec(x_5);
x_1154 = l_Lean_Expr_proj___override(x_1145, x_1146, x_1150);
lean_ctor_set(x_1148, 0, x_1154);
return x_1148;
}
else
{
lean_dec(x_1150);
lean_dec(x_1146);
lean_dec(x_1145);
lean_ctor_set(x_1148, 0, x_5);
return x_1148;
}
}
else
{
lean_object* x_1155; lean_object* x_1156; size_t x_1157; size_t x_1158; uint8_t x_1159; 
x_1155 = lean_ctor_get(x_1148, 0);
x_1156 = lean_ctor_get(x_1148, 1);
lean_inc(x_1156);
lean_inc(x_1155);
lean_dec(x_1148);
x_1157 = lean_ptr_addr(x_1147);
lean_dec(x_1147);
x_1158 = lean_ptr_addr(x_1155);
x_1159 = lean_usize_dec_eq(x_1157, x_1158);
if (x_1159 == 0)
{
lean_object* x_1160; lean_object* x_1161; 
lean_dec(x_5);
x_1160 = l_Lean_Expr_proj___override(x_1145, x_1146, x_1155);
x_1161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1161, 0, x_1160);
lean_ctor_set(x_1161, 1, x_1156);
return x_1161;
}
else
{
lean_object* x_1162; 
lean_dec(x_1155);
lean_dec(x_1146);
lean_dec(x_1145);
x_1162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1162, 0, x_5);
lean_ctor_set(x_1162, 1, x_1156);
return x_1162;
}
}
}
else
{
uint8_t x_1163; 
lean_dec(x_1147);
lean_dec(x_1146);
lean_dec(x_1145);
lean_dec(x_5);
x_1163 = !lean_is_exclusive(x_1148);
if (x_1163 == 0)
{
return x_1148;
}
else
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; 
x_1164 = lean_ctor_get(x_1148, 0);
x_1165 = lean_ctor_get(x_1148, 1);
lean_inc(x_1165);
lean_inc(x_1164);
lean_dec(x_1148);
x_1166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1166, 0, x_1164);
lean_ctor_set(x_1166, 1, x_1165);
return x_1166;
}
}
}
default: 
{
lean_object* x_1167; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1167, 0, x_5);
lean_ctor_set(x_1167, 1, x_12);
return x_1167;
}
}
}
block_923:
{
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_5);
x_14 = l_Lean_Meta_isExprDefEq(x_5, x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_18);
lean_inc(x_1);
x_20 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_19);
x_23 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; size_t x_26; size_t x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ptr_addr(x_18);
lean_dec(x_18);
x_27 = lean_ptr_addr(x_21);
x_28 = lean_usize_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_19);
lean_dec(x_5);
x_29 = l_Lean_Expr_app___override(x_21, x_25);
lean_ctor_set(x_23, 0, x_29);
return x_23;
}
else
{
size_t x_30; size_t x_31; uint8_t x_32; 
x_30 = lean_ptr_addr(x_19);
lean_dec(x_19);
x_31 = lean_ptr_addr(x_25);
x_32 = lean_usize_dec_eq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_5);
x_33 = l_Lean_Expr_app___override(x_21, x_25);
lean_ctor_set(x_23, 0, x_33);
return x_23;
}
else
{
lean_dec(x_25);
lean_dec(x_21);
lean_ctor_set(x_23, 0, x_5);
return x_23;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_ptr_addr(x_18);
lean_dec(x_18);
x_37 = lean_ptr_addr(x_21);
x_38 = lean_usize_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_19);
lean_dec(x_5);
x_39 = l_Lean_Expr_app___override(x_21, x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
return x_40;
}
else
{
size_t x_41; size_t x_42; uint8_t x_43; 
x_41 = lean_ptr_addr(x_19);
lean_dec(x_19);
x_42 = lean_ptr_addr(x_34);
x_43 = lean_usize_dec_eq(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_5);
x_44 = l_Lean_Expr_app___override(x_21, x_34);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_35);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_34);
lean_dec(x_21);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_5);
lean_ctor_set(x_46, 1, x_35);
return x_46;
}
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_23);
if (x_47 == 0)
{
return x_23;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_23, 0);
x_49 = lean_ctor_get(x_23, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_23);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_20);
if (x_51 == 0)
{
return x_20;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_20, 0);
x_53 = lean_ctor_get(x_20, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_20);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
case 6:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_14, 1);
lean_inc(x_55);
lean_dec(x_14);
x_56 = lean_ctor_get(x_5, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_5, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_5, 2);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_57);
lean_inc(x_1);
x_60 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_57, x_6, x_7, x_8, x_9, x_10, x_11, x_55);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_6, x_63);
lean_dec(x_6);
lean_inc(x_58);
x_65 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_58, x_64, x_7, x_8, x_9, x_10, x_11, x_62);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; size_t x_69; size_t x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
x_68 = l_Lean_Expr_lam___override(x_56, x_57, x_58, x_59);
x_69 = lean_ptr_addr(x_57);
lean_dec(x_57);
x_70 = lean_ptr_addr(x_61);
x_71 = lean_usize_dec_eq(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_68);
lean_dec(x_58);
x_72 = l_Lean_Expr_lam___override(x_56, x_61, x_67, x_59);
lean_ctor_set(x_65, 0, x_72);
return x_65;
}
else
{
size_t x_73; size_t x_74; uint8_t x_75; 
x_73 = lean_ptr_addr(x_58);
lean_dec(x_58);
x_74 = lean_ptr_addr(x_67);
x_75 = lean_usize_dec_eq(x_73, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_68);
x_76 = l_Lean_Expr_lam___override(x_56, x_61, x_67, x_59);
lean_ctor_set(x_65, 0, x_76);
return x_65;
}
else
{
uint8_t x_77; 
x_77 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_59, x_59);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_68);
x_78 = l_Lean_Expr_lam___override(x_56, x_61, x_67, x_59);
lean_ctor_set(x_65, 0, x_78);
return x_65;
}
else
{
lean_dec(x_67);
lean_dec(x_61);
lean_dec(x_56);
lean_ctor_set(x_65, 0, x_68);
return x_65;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; size_t x_82; size_t x_83; uint8_t x_84; 
x_79 = lean_ctor_get(x_65, 0);
x_80 = lean_ctor_get(x_65, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_65);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
x_81 = l_Lean_Expr_lam___override(x_56, x_57, x_58, x_59);
x_82 = lean_ptr_addr(x_57);
lean_dec(x_57);
x_83 = lean_ptr_addr(x_61);
x_84 = lean_usize_dec_eq(x_82, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_81);
lean_dec(x_58);
x_85 = l_Lean_Expr_lam___override(x_56, x_61, x_79, x_59);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_80);
return x_86;
}
else
{
size_t x_87; size_t x_88; uint8_t x_89; 
x_87 = lean_ptr_addr(x_58);
lean_dec(x_58);
x_88 = lean_ptr_addr(x_79);
x_89 = lean_usize_dec_eq(x_87, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_81);
x_90 = l_Lean_Expr_lam___override(x_56, x_61, x_79, x_59);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_80);
return x_91;
}
else
{
uint8_t x_92; 
x_92 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_59, x_59);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_81);
x_93 = l_Lean_Expr_lam___override(x_56, x_61, x_79, x_59);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_80);
return x_94;
}
else
{
lean_object* x_95; 
lean_dec(x_79);
lean_dec(x_61);
lean_dec(x_56);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_81);
lean_ctor_set(x_95, 1, x_80);
return x_95;
}
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
x_96 = !lean_is_exclusive(x_65);
if (x_96 == 0)
{
return x_65;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_65, 0);
x_98 = lean_ctor_get(x_65, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_65);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_60);
if (x_100 == 0)
{
return x_60;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_60, 0);
x_102 = lean_ctor_get(x_60, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_60);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
case 7:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_14, 1);
lean_inc(x_104);
lean_dec(x_14);
x_105 = lean_ctor_get(x_5, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_5, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_5, 2);
lean_inc(x_107);
x_108 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_106);
lean_inc(x_1);
x_109 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_106, x_6, x_7, x_8, x_9, x_10, x_11, x_104);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_nat_add(x_6, x_112);
lean_dec(x_6);
lean_inc(x_107);
x_114 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_107, x_113, x_7, x_8, x_9, x_10, x_11, x_111);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; size_t x_118; size_t x_119; uint8_t x_120; 
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
x_117 = l_Lean_Expr_forallE___override(x_105, x_106, x_107, x_108);
x_118 = lean_ptr_addr(x_106);
lean_dec(x_106);
x_119 = lean_ptr_addr(x_110);
x_120 = lean_usize_dec_eq(x_118, x_119);
if (x_120 == 0)
{
lean_object* x_121; 
lean_dec(x_117);
lean_dec(x_107);
x_121 = l_Lean_Expr_forallE___override(x_105, x_110, x_116, x_108);
lean_ctor_set(x_114, 0, x_121);
return x_114;
}
else
{
size_t x_122; size_t x_123; uint8_t x_124; 
x_122 = lean_ptr_addr(x_107);
lean_dec(x_107);
x_123 = lean_ptr_addr(x_116);
x_124 = lean_usize_dec_eq(x_122, x_123);
if (x_124 == 0)
{
lean_object* x_125; 
lean_dec(x_117);
x_125 = l_Lean_Expr_forallE___override(x_105, x_110, x_116, x_108);
lean_ctor_set(x_114, 0, x_125);
return x_114;
}
else
{
uint8_t x_126; 
x_126 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_108, x_108);
if (x_126 == 0)
{
lean_object* x_127; 
lean_dec(x_117);
x_127 = l_Lean_Expr_forallE___override(x_105, x_110, x_116, x_108);
lean_ctor_set(x_114, 0, x_127);
return x_114;
}
else
{
lean_dec(x_116);
lean_dec(x_110);
lean_dec(x_105);
lean_ctor_set(x_114, 0, x_117);
return x_114;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; size_t x_131; size_t x_132; uint8_t x_133; 
x_128 = lean_ctor_get(x_114, 0);
x_129 = lean_ctor_get(x_114, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_114);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
x_130 = l_Lean_Expr_forallE___override(x_105, x_106, x_107, x_108);
x_131 = lean_ptr_addr(x_106);
lean_dec(x_106);
x_132 = lean_ptr_addr(x_110);
x_133 = lean_usize_dec_eq(x_131, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_130);
lean_dec(x_107);
x_134 = l_Lean_Expr_forallE___override(x_105, x_110, x_128, x_108);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_129);
return x_135;
}
else
{
size_t x_136; size_t x_137; uint8_t x_138; 
x_136 = lean_ptr_addr(x_107);
lean_dec(x_107);
x_137 = lean_ptr_addr(x_128);
x_138 = lean_usize_dec_eq(x_136, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_130);
x_139 = l_Lean_Expr_forallE___override(x_105, x_110, x_128, x_108);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_129);
return x_140;
}
else
{
uint8_t x_141; 
x_141 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_108, x_108);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_130);
x_142 = l_Lean_Expr_forallE___override(x_105, x_110, x_128, x_108);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_129);
return x_143;
}
else
{
lean_object* x_144; 
lean_dec(x_128);
lean_dec(x_110);
lean_dec(x_105);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_130);
lean_ctor_set(x_144, 1, x_129);
return x_144;
}
}
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_110);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
x_145 = !lean_is_exclusive(x_114);
if (x_145 == 0)
{
return x_114;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_114, 0);
x_147 = lean_ctor_get(x_114, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_114);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_109);
if (x_149 == 0)
{
return x_109;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_109, 0);
x_151 = lean_ctor_get(x_109, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_109);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
case 8:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; 
x_153 = lean_ctor_get(x_14, 1);
lean_inc(x_153);
lean_dec(x_14);
x_154 = lean_ctor_get(x_5, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_5, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_5, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_5, 3);
lean_inc(x_157);
x_158 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_155);
lean_inc(x_1);
x_159 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_155, x_6, x_7, x_8, x_9, x_10, x_11, x_153);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_156);
lean_inc(x_1);
x_162 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_156, x_6, x_7, x_8, x_9, x_10, x_11, x_161);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_unsigned_to_nat(1u);
x_166 = lean_nat_add(x_6, x_165);
lean_dec(x_6);
lean_inc(x_157);
x_167 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_157, x_166, x_7, x_8, x_9, x_10, x_11, x_164);
if (lean_obj_tag(x_167) == 0)
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
lean_object* x_169; size_t x_170; size_t x_171; uint8_t x_172; 
x_169 = lean_ctor_get(x_167, 0);
x_170 = lean_ptr_addr(x_155);
lean_dec(x_155);
x_171 = lean_ptr_addr(x_160);
x_172 = lean_usize_dec_eq(x_170, x_171);
if (x_172 == 0)
{
lean_object* x_173; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_5);
x_173 = l_Lean_Expr_letE___override(x_154, x_160, x_163, x_169, x_158);
lean_ctor_set(x_167, 0, x_173);
return x_167;
}
else
{
size_t x_174; size_t x_175; uint8_t x_176; 
x_174 = lean_ptr_addr(x_156);
lean_dec(x_156);
x_175 = lean_ptr_addr(x_163);
x_176 = lean_usize_dec_eq(x_174, x_175);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_157);
lean_dec(x_5);
x_177 = l_Lean_Expr_letE___override(x_154, x_160, x_163, x_169, x_158);
lean_ctor_set(x_167, 0, x_177);
return x_167;
}
else
{
size_t x_178; size_t x_179; uint8_t x_180; 
x_178 = lean_ptr_addr(x_157);
lean_dec(x_157);
x_179 = lean_ptr_addr(x_169);
x_180 = lean_usize_dec_eq(x_178, x_179);
if (x_180 == 0)
{
lean_object* x_181; 
lean_dec(x_5);
x_181 = l_Lean_Expr_letE___override(x_154, x_160, x_163, x_169, x_158);
lean_ctor_set(x_167, 0, x_181);
return x_167;
}
else
{
lean_dec(x_169);
lean_dec(x_163);
lean_dec(x_160);
lean_dec(x_154);
lean_ctor_set(x_167, 0, x_5);
return x_167;
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; size_t x_184; size_t x_185; uint8_t x_186; 
x_182 = lean_ctor_get(x_167, 0);
x_183 = lean_ctor_get(x_167, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_167);
x_184 = lean_ptr_addr(x_155);
lean_dec(x_155);
x_185 = lean_ptr_addr(x_160);
x_186 = lean_usize_dec_eq(x_184, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_5);
x_187 = l_Lean_Expr_letE___override(x_154, x_160, x_163, x_182, x_158);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_183);
return x_188;
}
else
{
size_t x_189; size_t x_190; uint8_t x_191; 
x_189 = lean_ptr_addr(x_156);
lean_dec(x_156);
x_190 = lean_ptr_addr(x_163);
x_191 = lean_usize_dec_eq(x_189, x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_157);
lean_dec(x_5);
x_192 = l_Lean_Expr_letE___override(x_154, x_160, x_163, x_182, x_158);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_183);
return x_193;
}
else
{
size_t x_194; size_t x_195; uint8_t x_196; 
x_194 = lean_ptr_addr(x_157);
lean_dec(x_157);
x_195 = lean_ptr_addr(x_182);
x_196 = lean_usize_dec_eq(x_194, x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_5);
x_197 = l_Lean_Expr_letE___override(x_154, x_160, x_163, x_182, x_158);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_183);
return x_198;
}
else
{
lean_object* x_199; 
lean_dec(x_182);
lean_dec(x_163);
lean_dec(x_160);
lean_dec(x_154);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_5);
lean_ctor_set(x_199, 1, x_183);
return x_199;
}
}
}
}
}
else
{
uint8_t x_200; 
lean_dec(x_163);
lean_dec(x_160);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_5);
x_200 = !lean_is_exclusive(x_167);
if (x_200 == 0)
{
return x_167;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_167, 0);
x_202 = lean_ctor_get(x_167, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_167);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_160);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_204 = !lean_is_exclusive(x_162);
if (x_204 == 0)
{
return x_162;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_162, 0);
x_206 = lean_ctor_get(x_162, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_162);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_159);
if (x_208 == 0)
{
return x_159;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_159, 0);
x_210 = lean_ctor_get(x_159, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_159);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
case 10:
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_14, 1);
lean_inc(x_212);
lean_dec(x_14);
x_213 = lean_ctor_get(x_5, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_5, 1);
lean_inc(x_214);
lean_inc(x_214);
x_215 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_214, x_6, x_7, x_8, x_9, x_10, x_11, x_212);
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; size_t x_218; size_t x_219; uint8_t x_220; 
x_217 = lean_ctor_get(x_215, 0);
x_218 = lean_ptr_addr(x_214);
lean_dec(x_214);
x_219 = lean_ptr_addr(x_217);
x_220 = lean_usize_dec_eq(x_218, x_219);
if (x_220 == 0)
{
lean_object* x_221; 
lean_dec(x_5);
x_221 = l_Lean_Expr_mdata___override(x_213, x_217);
lean_ctor_set(x_215, 0, x_221);
return x_215;
}
else
{
lean_dec(x_217);
lean_dec(x_213);
lean_ctor_set(x_215, 0, x_5);
return x_215;
}
}
else
{
lean_object* x_222; lean_object* x_223; size_t x_224; size_t x_225; uint8_t x_226; 
x_222 = lean_ctor_get(x_215, 0);
x_223 = lean_ctor_get(x_215, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_215);
x_224 = lean_ptr_addr(x_214);
lean_dec(x_214);
x_225 = lean_ptr_addr(x_222);
x_226 = lean_usize_dec_eq(x_224, x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
lean_dec(x_5);
x_227 = l_Lean_Expr_mdata___override(x_213, x_222);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_223);
return x_228;
}
else
{
lean_object* x_229; 
lean_dec(x_222);
lean_dec(x_213);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_5);
lean_ctor_set(x_229, 1, x_223);
return x_229;
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_5);
x_230 = !lean_is_exclusive(x_215);
if (x_230 == 0)
{
return x_215;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_215, 0);
x_232 = lean_ctor_get(x_215, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_215);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
case 11:
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_14, 1);
lean_inc(x_234);
lean_dec(x_14);
x_235 = lean_ctor_get(x_5, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_5, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_5, 2);
lean_inc(x_237);
lean_inc(x_237);
x_238 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_237, x_6, x_7, x_8, x_9, x_10, x_11, x_234);
if (lean_obj_tag(x_238) == 0)
{
uint8_t x_239; 
x_239 = !lean_is_exclusive(x_238);
if (x_239 == 0)
{
lean_object* x_240; size_t x_241; size_t x_242; uint8_t x_243; 
x_240 = lean_ctor_get(x_238, 0);
x_241 = lean_ptr_addr(x_237);
lean_dec(x_237);
x_242 = lean_ptr_addr(x_240);
x_243 = lean_usize_dec_eq(x_241, x_242);
if (x_243 == 0)
{
lean_object* x_244; 
lean_dec(x_5);
x_244 = l_Lean_Expr_proj___override(x_235, x_236, x_240);
lean_ctor_set(x_238, 0, x_244);
return x_238;
}
else
{
lean_dec(x_240);
lean_dec(x_236);
lean_dec(x_235);
lean_ctor_set(x_238, 0, x_5);
return x_238;
}
}
else
{
lean_object* x_245; lean_object* x_246; size_t x_247; size_t x_248; uint8_t x_249; 
x_245 = lean_ctor_get(x_238, 0);
x_246 = lean_ctor_get(x_238, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_238);
x_247 = lean_ptr_addr(x_237);
lean_dec(x_237);
x_248 = lean_ptr_addr(x_245);
x_249 = lean_usize_dec_eq(x_247, x_248);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_5);
x_250 = l_Lean_Expr_proj___override(x_235, x_236, x_245);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_246);
return x_251;
}
else
{
lean_object* x_252; 
lean_dec(x_245);
lean_dec(x_236);
lean_dec(x_235);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_5);
lean_ctor_set(x_252, 1, x_246);
return x_252;
}
}
}
else
{
uint8_t x_253; 
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_5);
x_253 = !lean_is_exclusive(x_238);
if (x_253 == 0)
{
return x_238;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_238, 0);
x_255 = lean_ctor_get(x_238, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_238);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
default: 
{
uint8_t x_257; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_257 = !lean_is_exclusive(x_14);
if (x_257 == 0)
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_14, 0);
lean_dec(x_258);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
else
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_14, 1);
lean_inc(x_259);
lean_dec(x_14);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_5);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_261 = lean_ctor_get(x_14, 1);
lean_inc(x_261);
lean_dec(x_14);
x_262 = lean_st_ref_get(x_7, x_261);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_unsigned_to_nat(1u);
x_266 = lean_nat_add(x_263, x_265);
x_267 = lean_st_ref_set(x_7, x_266, x_264);
x_268 = !lean_is_exclusive(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_269 = lean_ctor_get(x_267, 1);
x_270 = lean_ctor_get(x_267, 0);
lean_dec(x_270);
x_271 = l_Lean_Occurrences_contains(x_2, x_263);
lean_dec(x_263);
if (x_271 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_free_object(x_267);
x_272 = lean_ctor_get(x_5, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_5, 1);
lean_inc(x_273);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_272);
lean_inc(x_1);
x_274 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_272, x_6, x_7, x_8, x_9, x_10, x_11, x_269);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
lean_inc(x_273);
x_277 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_273, x_6, x_7, x_8, x_9, x_10, x_11, x_276);
if (lean_obj_tag(x_277) == 0)
{
uint8_t x_278; 
x_278 = !lean_is_exclusive(x_277);
if (x_278 == 0)
{
lean_object* x_279; size_t x_280; size_t x_281; uint8_t x_282; 
x_279 = lean_ctor_get(x_277, 0);
x_280 = lean_ptr_addr(x_272);
lean_dec(x_272);
x_281 = lean_ptr_addr(x_275);
x_282 = lean_usize_dec_eq(x_280, x_281);
if (x_282 == 0)
{
lean_object* x_283; 
lean_dec(x_273);
lean_dec(x_5);
x_283 = l_Lean_Expr_app___override(x_275, x_279);
lean_ctor_set(x_277, 0, x_283);
return x_277;
}
else
{
size_t x_284; size_t x_285; uint8_t x_286; 
x_284 = lean_ptr_addr(x_273);
lean_dec(x_273);
x_285 = lean_ptr_addr(x_279);
x_286 = lean_usize_dec_eq(x_284, x_285);
if (x_286 == 0)
{
lean_object* x_287; 
lean_dec(x_5);
x_287 = l_Lean_Expr_app___override(x_275, x_279);
lean_ctor_set(x_277, 0, x_287);
return x_277;
}
else
{
lean_dec(x_279);
lean_dec(x_275);
lean_ctor_set(x_277, 0, x_5);
return x_277;
}
}
}
else
{
lean_object* x_288; lean_object* x_289; size_t x_290; size_t x_291; uint8_t x_292; 
x_288 = lean_ctor_get(x_277, 0);
x_289 = lean_ctor_get(x_277, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_277);
x_290 = lean_ptr_addr(x_272);
lean_dec(x_272);
x_291 = lean_ptr_addr(x_275);
x_292 = lean_usize_dec_eq(x_290, x_291);
if (x_292 == 0)
{
lean_object* x_293; lean_object* x_294; 
lean_dec(x_273);
lean_dec(x_5);
x_293 = l_Lean_Expr_app___override(x_275, x_288);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_289);
return x_294;
}
else
{
size_t x_295; size_t x_296; uint8_t x_297; 
x_295 = lean_ptr_addr(x_273);
lean_dec(x_273);
x_296 = lean_ptr_addr(x_288);
x_297 = lean_usize_dec_eq(x_295, x_296);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_5);
x_298 = l_Lean_Expr_app___override(x_275, x_288);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_289);
return x_299;
}
else
{
lean_object* x_300; 
lean_dec(x_288);
lean_dec(x_275);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_5);
lean_ctor_set(x_300, 1, x_289);
return x_300;
}
}
}
}
else
{
uint8_t x_301; 
lean_dec(x_275);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_5);
x_301 = !lean_is_exclusive(x_277);
if (x_301 == 0)
{
return x_277;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_277, 0);
x_303 = lean_ctor_get(x_277, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_277);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
return x_304;
}
}
}
else
{
uint8_t x_305; 
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_305 = !lean_is_exclusive(x_274);
if (x_305 == 0)
{
return x_274;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_274, 0);
x_307 = lean_ctor_get(x_274, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_274);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
case 6:
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; 
lean_free_object(x_267);
x_309 = lean_ctor_get(x_5, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_5, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_5, 2);
lean_inc(x_311);
x_312 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_310);
lean_inc(x_1);
x_313 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_310, x_6, x_7, x_8, x_9, x_10, x_11, x_269);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = lean_nat_add(x_6, x_265);
lean_dec(x_6);
lean_inc(x_311);
x_317 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_311, x_316, x_7, x_8, x_9, x_10, x_11, x_315);
if (lean_obj_tag(x_317) == 0)
{
uint8_t x_318; 
x_318 = !lean_is_exclusive(x_317);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; size_t x_321; size_t x_322; uint8_t x_323; 
x_319 = lean_ctor_get(x_317, 0);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
x_320 = l_Lean_Expr_lam___override(x_309, x_310, x_311, x_312);
x_321 = lean_ptr_addr(x_310);
lean_dec(x_310);
x_322 = lean_ptr_addr(x_314);
x_323 = lean_usize_dec_eq(x_321, x_322);
if (x_323 == 0)
{
lean_object* x_324; 
lean_dec(x_320);
lean_dec(x_311);
x_324 = l_Lean_Expr_lam___override(x_309, x_314, x_319, x_312);
lean_ctor_set(x_317, 0, x_324);
return x_317;
}
else
{
size_t x_325; size_t x_326; uint8_t x_327; 
x_325 = lean_ptr_addr(x_311);
lean_dec(x_311);
x_326 = lean_ptr_addr(x_319);
x_327 = lean_usize_dec_eq(x_325, x_326);
if (x_327 == 0)
{
lean_object* x_328; 
lean_dec(x_320);
x_328 = l_Lean_Expr_lam___override(x_309, x_314, x_319, x_312);
lean_ctor_set(x_317, 0, x_328);
return x_317;
}
else
{
uint8_t x_329; 
x_329 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_312, x_312);
if (x_329 == 0)
{
lean_object* x_330; 
lean_dec(x_320);
x_330 = l_Lean_Expr_lam___override(x_309, x_314, x_319, x_312);
lean_ctor_set(x_317, 0, x_330);
return x_317;
}
else
{
lean_dec(x_319);
lean_dec(x_314);
lean_dec(x_309);
lean_ctor_set(x_317, 0, x_320);
return x_317;
}
}
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; size_t x_334; size_t x_335; uint8_t x_336; 
x_331 = lean_ctor_get(x_317, 0);
x_332 = lean_ctor_get(x_317, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_317);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
x_333 = l_Lean_Expr_lam___override(x_309, x_310, x_311, x_312);
x_334 = lean_ptr_addr(x_310);
lean_dec(x_310);
x_335 = lean_ptr_addr(x_314);
x_336 = lean_usize_dec_eq(x_334, x_335);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; 
lean_dec(x_333);
lean_dec(x_311);
x_337 = l_Lean_Expr_lam___override(x_309, x_314, x_331, x_312);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_332);
return x_338;
}
else
{
size_t x_339; size_t x_340; uint8_t x_341; 
x_339 = lean_ptr_addr(x_311);
lean_dec(x_311);
x_340 = lean_ptr_addr(x_331);
x_341 = lean_usize_dec_eq(x_339, x_340);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; 
lean_dec(x_333);
x_342 = l_Lean_Expr_lam___override(x_309, x_314, x_331, x_312);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_332);
return x_343;
}
else
{
uint8_t x_344; 
x_344 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_312, x_312);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_333);
x_345 = l_Lean_Expr_lam___override(x_309, x_314, x_331, x_312);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_332);
return x_346;
}
else
{
lean_object* x_347; 
lean_dec(x_331);
lean_dec(x_314);
lean_dec(x_309);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_333);
lean_ctor_set(x_347, 1, x_332);
return x_347;
}
}
}
}
}
else
{
uint8_t x_348; 
lean_dec(x_314);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
x_348 = !lean_is_exclusive(x_317);
if (x_348 == 0)
{
return x_317;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_317, 0);
x_350 = lean_ctor_get(x_317, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_317);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
return x_351;
}
}
}
else
{
uint8_t x_352; 
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_352 = !lean_is_exclusive(x_313);
if (x_352 == 0)
{
return x_313;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_313, 0);
x_354 = lean_ctor_get(x_313, 1);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_313);
x_355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set(x_355, 1, x_354);
return x_355;
}
}
}
case 7:
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; 
lean_free_object(x_267);
x_356 = lean_ctor_get(x_5, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_5, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_5, 2);
lean_inc(x_358);
x_359 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_357);
lean_inc(x_1);
x_360 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_357, x_6, x_7, x_8, x_9, x_10, x_11, x_269);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = lean_nat_add(x_6, x_265);
lean_dec(x_6);
lean_inc(x_358);
x_364 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_358, x_363, x_7, x_8, x_9, x_10, x_11, x_362);
if (lean_obj_tag(x_364) == 0)
{
uint8_t x_365; 
x_365 = !lean_is_exclusive(x_364);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; size_t x_368; size_t x_369; uint8_t x_370; 
x_366 = lean_ctor_get(x_364, 0);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
x_367 = l_Lean_Expr_forallE___override(x_356, x_357, x_358, x_359);
x_368 = lean_ptr_addr(x_357);
lean_dec(x_357);
x_369 = lean_ptr_addr(x_361);
x_370 = lean_usize_dec_eq(x_368, x_369);
if (x_370 == 0)
{
lean_object* x_371; 
lean_dec(x_367);
lean_dec(x_358);
x_371 = l_Lean_Expr_forallE___override(x_356, x_361, x_366, x_359);
lean_ctor_set(x_364, 0, x_371);
return x_364;
}
else
{
size_t x_372; size_t x_373; uint8_t x_374; 
x_372 = lean_ptr_addr(x_358);
lean_dec(x_358);
x_373 = lean_ptr_addr(x_366);
x_374 = lean_usize_dec_eq(x_372, x_373);
if (x_374 == 0)
{
lean_object* x_375; 
lean_dec(x_367);
x_375 = l_Lean_Expr_forallE___override(x_356, x_361, x_366, x_359);
lean_ctor_set(x_364, 0, x_375);
return x_364;
}
else
{
uint8_t x_376; 
x_376 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_359, x_359);
if (x_376 == 0)
{
lean_object* x_377; 
lean_dec(x_367);
x_377 = l_Lean_Expr_forallE___override(x_356, x_361, x_366, x_359);
lean_ctor_set(x_364, 0, x_377);
return x_364;
}
else
{
lean_dec(x_366);
lean_dec(x_361);
lean_dec(x_356);
lean_ctor_set(x_364, 0, x_367);
return x_364;
}
}
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; size_t x_381; size_t x_382; uint8_t x_383; 
x_378 = lean_ctor_get(x_364, 0);
x_379 = lean_ctor_get(x_364, 1);
lean_inc(x_379);
lean_inc(x_378);
lean_dec(x_364);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
x_380 = l_Lean_Expr_forallE___override(x_356, x_357, x_358, x_359);
x_381 = lean_ptr_addr(x_357);
lean_dec(x_357);
x_382 = lean_ptr_addr(x_361);
x_383 = lean_usize_dec_eq(x_381, x_382);
if (x_383 == 0)
{
lean_object* x_384; lean_object* x_385; 
lean_dec(x_380);
lean_dec(x_358);
x_384 = l_Lean_Expr_forallE___override(x_356, x_361, x_378, x_359);
x_385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_379);
return x_385;
}
else
{
size_t x_386; size_t x_387; uint8_t x_388; 
x_386 = lean_ptr_addr(x_358);
lean_dec(x_358);
x_387 = lean_ptr_addr(x_378);
x_388 = lean_usize_dec_eq(x_386, x_387);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; 
lean_dec(x_380);
x_389 = l_Lean_Expr_forallE___override(x_356, x_361, x_378, x_359);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_379);
return x_390;
}
else
{
uint8_t x_391; 
x_391 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_359, x_359);
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; 
lean_dec(x_380);
x_392 = l_Lean_Expr_forallE___override(x_356, x_361, x_378, x_359);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_379);
return x_393;
}
else
{
lean_object* x_394; 
lean_dec(x_378);
lean_dec(x_361);
lean_dec(x_356);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_380);
lean_ctor_set(x_394, 1, x_379);
return x_394;
}
}
}
}
}
else
{
uint8_t x_395; 
lean_dec(x_361);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
x_395 = !lean_is_exclusive(x_364);
if (x_395 == 0)
{
return x_364;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_364, 0);
x_397 = lean_ctor_get(x_364, 1);
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_364);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_397);
return x_398;
}
}
}
else
{
uint8_t x_399; 
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_399 = !lean_is_exclusive(x_360);
if (x_399 == 0)
{
return x_360;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_360, 0);
x_401 = lean_ctor_get(x_360, 1);
lean_inc(x_401);
lean_inc(x_400);
lean_dec(x_360);
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
return x_402;
}
}
}
case 8:
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; lean_object* x_408; 
lean_free_object(x_267);
x_403 = lean_ctor_get(x_5, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_5, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_5, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_5, 3);
lean_inc(x_406);
x_407 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_404);
lean_inc(x_1);
x_408 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_404, x_6, x_7, x_8, x_9, x_10, x_11, x_269);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_405);
lean_inc(x_1);
x_411 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_405, x_6, x_7, x_8, x_9, x_10, x_11, x_410);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = lean_nat_add(x_6, x_265);
lean_dec(x_6);
lean_inc(x_406);
x_415 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_406, x_414, x_7, x_8, x_9, x_10, x_11, x_413);
if (lean_obj_tag(x_415) == 0)
{
uint8_t x_416; 
x_416 = !lean_is_exclusive(x_415);
if (x_416 == 0)
{
lean_object* x_417; size_t x_418; size_t x_419; uint8_t x_420; 
x_417 = lean_ctor_get(x_415, 0);
x_418 = lean_ptr_addr(x_404);
lean_dec(x_404);
x_419 = lean_ptr_addr(x_409);
x_420 = lean_usize_dec_eq(x_418, x_419);
if (x_420 == 0)
{
lean_object* x_421; 
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_5);
x_421 = l_Lean_Expr_letE___override(x_403, x_409, x_412, x_417, x_407);
lean_ctor_set(x_415, 0, x_421);
return x_415;
}
else
{
size_t x_422; size_t x_423; uint8_t x_424; 
x_422 = lean_ptr_addr(x_405);
lean_dec(x_405);
x_423 = lean_ptr_addr(x_412);
x_424 = lean_usize_dec_eq(x_422, x_423);
if (x_424 == 0)
{
lean_object* x_425; 
lean_dec(x_406);
lean_dec(x_5);
x_425 = l_Lean_Expr_letE___override(x_403, x_409, x_412, x_417, x_407);
lean_ctor_set(x_415, 0, x_425);
return x_415;
}
else
{
size_t x_426; size_t x_427; uint8_t x_428; 
x_426 = lean_ptr_addr(x_406);
lean_dec(x_406);
x_427 = lean_ptr_addr(x_417);
x_428 = lean_usize_dec_eq(x_426, x_427);
if (x_428 == 0)
{
lean_object* x_429; 
lean_dec(x_5);
x_429 = l_Lean_Expr_letE___override(x_403, x_409, x_412, x_417, x_407);
lean_ctor_set(x_415, 0, x_429);
return x_415;
}
else
{
lean_dec(x_417);
lean_dec(x_412);
lean_dec(x_409);
lean_dec(x_403);
lean_ctor_set(x_415, 0, x_5);
return x_415;
}
}
}
}
else
{
lean_object* x_430; lean_object* x_431; size_t x_432; size_t x_433; uint8_t x_434; 
x_430 = lean_ctor_get(x_415, 0);
x_431 = lean_ctor_get(x_415, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_415);
x_432 = lean_ptr_addr(x_404);
lean_dec(x_404);
x_433 = lean_ptr_addr(x_409);
x_434 = lean_usize_dec_eq(x_432, x_433);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; 
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_5);
x_435 = l_Lean_Expr_letE___override(x_403, x_409, x_412, x_430, x_407);
x_436 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_431);
return x_436;
}
else
{
size_t x_437; size_t x_438; uint8_t x_439; 
x_437 = lean_ptr_addr(x_405);
lean_dec(x_405);
x_438 = lean_ptr_addr(x_412);
x_439 = lean_usize_dec_eq(x_437, x_438);
if (x_439 == 0)
{
lean_object* x_440; lean_object* x_441; 
lean_dec(x_406);
lean_dec(x_5);
x_440 = l_Lean_Expr_letE___override(x_403, x_409, x_412, x_430, x_407);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_431);
return x_441;
}
else
{
size_t x_442; size_t x_443; uint8_t x_444; 
x_442 = lean_ptr_addr(x_406);
lean_dec(x_406);
x_443 = lean_ptr_addr(x_430);
x_444 = lean_usize_dec_eq(x_442, x_443);
if (x_444 == 0)
{
lean_object* x_445; lean_object* x_446; 
lean_dec(x_5);
x_445 = l_Lean_Expr_letE___override(x_403, x_409, x_412, x_430, x_407);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_431);
return x_446;
}
else
{
lean_object* x_447; 
lean_dec(x_430);
lean_dec(x_412);
lean_dec(x_409);
lean_dec(x_403);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_5);
lean_ctor_set(x_447, 1, x_431);
return x_447;
}
}
}
}
}
else
{
uint8_t x_448; 
lean_dec(x_412);
lean_dec(x_409);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_5);
x_448 = !lean_is_exclusive(x_415);
if (x_448 == 0)
{
return x_415;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_415, 0);
x_450 = lean_ctor_get(x_415, 1);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_415);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_450);
return x_451;
}
}
}
else
{
uint8_t x_452; 
lean_dec(x_409);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_452 = !lean_is_exclusive(x_411);
if (x_452 == 0)
{
return x_411;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_411, 0);
x_454 = lean_ctor_get(x_411, 1);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_411);
x_455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
return x_455;
}
}
}
else
{
uint8_t x_456; 
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_456 = !lean_is_exclusive(x_408);
if (x_456 == 0)
{
return x_408;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_408, 0);
x_458 = lean_ctor_get(x_408, 1);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_408);
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
return x_459;
}
}
}
case 10:
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_free_object(x_267);
x_460 = lean_ctor_get(x_5, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_5, 1);
lean_inc(x_461);
lean_inc(x_461);
x_462 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_461, x_6, x_7, x_8, x_9, x_10, x_11, x_269);
if (lean_obj_tag(x_462) == 0)
{
uint8_t x_463; 
x_463 = !lean_is_exclusive(x_462);
if (x_463 == 0)
{
lean_object* x_464; size_t x_465; size_t x_466; uint8_t x_467; 
x_464 = lean_ctor_get(x_462, 0);
x_465 = lean_ptr_addr(x_461);
lean_dec(x_461);
x_466 = lean_ptr_addr(x_464);
x_467 = lean_usize_dec_eq(x_465, x_466);
if (x_467 == 0)
{
lean_object* x_468; 
lean_dec(x_5);
x_468 = l_Lean_Expr_mdata___override(x_460, x_464);
lean_ctor_set(x_462, 0, x_468);
return x_462;
}
else
{
lean_dec(x_464);
lean_dec(x_460);
lean_ctor_set(x_462, 0, x_5);
return x_462;
}
}
else
{
lean_object* x_469; lean_object* x_470; size_t x_471; size_t x_472; uint8_t x_473; 
x_469 = lean_ctor_get(x_462, 0);
x_470 = lean_ctor_get(x_462, 1);
lean_inc(x_470);
lean_inc(x_469);
lean_dec(x_462);
x_471 = lean_ptr_addr(x_461);
lean_dec(x_461);
x_472 = lean_ptr_addr(x_469);
x_473 = lean_usize_dec_eq(x_471, x_472);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; 
lean_dec(x_5);
x_474 = l_Lean_Expr_mdata___override(x_460, x_469);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_474);
lean_ctor_set(x_475, 1, x_470);
return x_475;
}
else
{
lean_object* x_476; 
lean_dec(x_469);
lean_dec(x_460);
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_5);
lean_ctor_set(x_476, 1, x_470);
return x_476;
}
}
}
else
{
uint8_t x_477; 
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_5);
x_477 = !lean_is_exclusive(x_462);
if (x_477 == 0)
{
return x_462;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_478 = lean_ctor_get(x_462, 0);
x_479 = lean_ctor_get(x_462, 1);
lean_inc(x_479);
lean_inc(x_478);
lean_dec(x_462);
x_480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_480, 0, x_478);
lean_ctor_set(x_480, 1, x_479);
return x_480;
}
}
}
case 11:
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
lean_free_object(x_267);
x_481 = lean_ctor_get(x_5, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_5, 1);
lean_inc(x_482);
x_483 = lean_ctor_get(x_5, 2);
lean_inc(x_483);
lean_inc(x_483);
x_484 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_483, x_6, x_7, x_8, x_9, x_10, x_11, x_269);
if (lean_obj_tag(x_484) == 0)
{
uint8_t x_485; 
x_485 = !lean_is_exclusive(x_484);
if (x_485 == 0)
{
lean_object* x_486; size_t x_487; size_t x_488; uint8_t x_489; 
x_486 = lean_ctor_get(x_484, 0);
x_487 = lean_ptr_addr(x_483);
lean_dec(x_483);
x_488 = lean_ptr_addr(x_486);
x_489 = lean_usize_dec_eq(x_487, x_488);
if (x_489 == 0)
{
lean_object* x_490; 
lean_dec(x_5);
x_490 = l_Lean_Expr_proj___override(x_481, x_482, x_486);
lean_ctor_set(x_484, 0, x_490);
return x_484;
}
else
{
lean_dec(x_486);
lean_dec(x_482);
lean_dec(x_481);
lean_ctor_set(x_484, 0, x_5);
return x_484;
}
}
else
{
lean_object* x_491; lean_object* x_492; size_t x_493; size_t x_494; uint8_t x_495; 
x_491 = lean_ctor_get(x_484, 0);
x_492 = lean_ctor_get(x_484, 1);
lean_inc(x_492);
lean_inc(x_491);
lean_dec(x_484);
x_493 = lean_ptr_addr(x_483);
lean_dec(x_483);
x_494 = lean_ptr_addr(x_491);
x_495 = lean_usize_dec_eq(x_493, x_494);
if (x_495 == 0)
{
lean_object* x_496; lean_object* x_497; 
lean_dec(x_5);
x_496 = l_Lean_Expr_proj___override(x_481, x_482, x_491);
x_497 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set(x_497, 1, x_492);
return x_497;
}
else
{
lean_object* x_498; 
lean_dec(x_491);
lean_dec(x_482);
lean_dec(x_481);
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_5);
lean_ctor_set(x_498, 1, x_492);
return x_498;
}
}
}
else
{
uint8_t x_499; 
lean_dec(x_483);
lean_dec(x_482);
lean_dec(x_481);
lean_dec(x_5);
x_499 = !lean_is_exclusive(x_484);
if (x_499 == 0)
{
return x_484;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_500 = lean_ctor_get(x_484, 0);
x_501 = lean_ctor_get(x_484, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_484);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
return x_502;
}
}
}
default: 
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
lean_ctor_set(x_267, 0, x_5);
return x_267;
}
}
}
else
{
lean_object* x_503; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_503 = l_Lean_Expr_bvar___override(x_6);
lean_ctor_set(x_267, 0, x_503);
return x_267;
}
}
else
{
lean_object* x_504; uint8_t x_505; 
x_504 = lean_ctor_get(x_267, 1);
lean_inc(x_504);
lean_dec(x_267);
x_505 = l_Lean_Occurrences_contains(x_2, x_263);
lean_dec(x_263);
if (x_505 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_506 = lean_ctor_get(x_5, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_5, 1);
lean_inc(x_507);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_506);
lean_inc(x_1);
x_508 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_506, x_6, x_7, x_8, x_9, x_10, x_11, x_504);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
lean_inc(x_507);
x_511 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_507, x_6, x_7, x_8, x_9, x_10, x_11, x_510);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; size_t x_515; size_t x_516; uint8_t x_517; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_514 = x_511;
} else {
 lean_dec_ref(x_511);
 x_514 = lean_box(0);
}
x_515 = lean_ptr_addr(x_506);
lean_dec(x_506);
x_516 = lean_ptr_addr(x_509);
x_517 = lean_usize_dec_eq(x_515, x_516);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; 
lean_dec(x_507);
lean_dec(x_5);
x_518 = l_Lean_Expr_app___override(x_509, x_512);
if (lean_is_scalar(x_514)) {
 x_519 = lean_alloc_ctor(0, 2, 0);
} else {
 x_519 = x_514;
}
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_513);
return x_519;
}
else
{
size_t x_520; size_t x_521; uint8_t x_522; 
x_520 = lean_ptr_addr(x_507);
lean_dec(x_507);
x_521 = lean_ptr_addr(x_512);
x_522 = lean_usize_dec_eq(x_520, x_521);
if (x_522 == 0)
{
lean_object* x_523; lean_object* x_524; 
lean_dec(x_5);
x_523 = l_Lean_Expr_app___override(x_509, x_512);
if (lean_is_scalar(x_514)) {
 x_524 = lean_alloc_ctor(0, 2, 0);
} else {
 x_524 = x_514;
}
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_524, 1, x_513);
return x_524;
}
else
{
lean_object* x_525; 
lean_dec(x_512);
lean_dec(x_509);
if (lean_is_scalar(x_514)) {
 x_525 = lean_alloc_ctor(0, 2, 0);
} else {
 x_525 = x_514;
}
lean_ctor_set(x_525, 0, x_5);
lean_ctor_set(x_525, 1, x_513);
return x_525;
}
}
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
lean_dec(x_509);
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_5);
x_526 = lean_ctor_get(x_511, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_511, 1);
lean_inc(x_527);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_528 = x_511;
} else {
 lean_dec_ref(x_511);
 x_528 = lean_box(0);
}
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 2, 0);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_526);
lean_ctor_set(x_529, 1, x_527);
return x_529;
}
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_530 = lean_ctor_get(x_508, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_508, 1);
lean_inc(x_531);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_532 = x_508;
} else {
 lean_dec_ref(x_508);
 x_532 = lean_box(0);
}
if (lean_is_scalar(x_532)) {
 x_533 = lean_alloc_ctor(1, 2, 0);
} else {
 x_533 = x_532;
}
lean_ctor_set(x_533, 0, x_530);
lean_ctor_set(x_533, 1, x_531);
return x_533;
}
}
case 6:
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; lean_object* x_538; 
x_534 = lean_ctor_get(x_5, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_5, 1);
lean_inc(x_535);
x_536 = lean_ctor_get(x_5, 2);
lean_inc(x_536);
x_537 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_535);
lean_inc(x_1);
x_538 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_535, x_6, x_7, x_8, x_9, x_10, x_11, x_504);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_538, 1);
lean_inc(x_540);
lean_dec(x_538);
x_541 = lean_nat_add(x_6, x_265);
lean_dec(x_6);
lean_inc(x_536);
x_542 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_536, x_541, x_7, x_8, x_9, x_10, x_11, x_540);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; size_t x_547; size_t x_548; uint8_t x_549; 
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_542, 1);
lean_inc(x_544);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 lean_ctor_release(x_542, 1);
 x_545 = x_542;
} else {
 lean_dec_ref(x_542);
 x_545 = lean_box(0);
}
lean_inc(x_536);
lean_inc(x_535);
lean_inc(x_534);
x_546 = l_Lean_Expr_lam___override(x_534, x_535, x_536, x_537);
x_547 = lean_ptr_addr(x_535);
lean_dec(x_535);
x_548 = lean_ptr_addr(x_539);
x_549 = lean_usize_dec_eq(x_547, x_548);
if (x_549 == 0)
{
lean_object* x_550; lean_object* x_551; 
lean_dec(x_546);
lean_dec(x_536);
x_550 = l_Lean_Expr_lam___override(x_534, x_539, x_543, x_537);
if (lean_is_scalar(x_545)) {
 x_551 = lean_alloc_ctor(0, 2, 0);
} else {
 x_551 = x_545;
}
lean_ctor_set(x_551, 0, x_550);
lean_ctor_set(x_551, 1, x_544);
return x_551;
}
else
{
size_t x_552; size_t x_553; uint8_t x_554; 
x_552 = lean_ptr_addr(x_536);
lean_dec(x_536);
x_553 = lean_ptr_addr(x_543);
x_554 = lean_usize_dec_eq(x_552, x_553);
if (x_554 == 0)
{
lean_object* x_555; lean_object* x_556; 
lean_dec(x_546);
x_555 = l_Lean_Expr_lam___override(x_534, x_539, x_543, x_537);
if (lean_is_scalar(x_545)) {
 x_556 = lean_alloc_ctor(0, 2, 0);
} else {
 x_556 = x_545;
}
lean_ctor_set(x_556, 0, x_555);
lean_ctor_set(x_556, 1, x_544);
return x_556;
}
else
{
uint8_t x_557; 
x_557 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_537, x_537);
if (x_557 == 0)
{
lean_object* x_558; lean_object* x_559; 
lean_dec(x_546);
x_558 = l_Lean_Expr_lam___override(x_534, x_539, x_543, x_537);
if (lean_is_scalar(x_545)) {
 x_559 = lean_alloc_ctor(0, 2, 0);
} else {
 x_559 = x_545;
}
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_544);
return x_559;
}
else
{
lean_object* x_560; 
lean_dec(x_543);
lean_dec(x_539);
lean_dec(x_534);
if (lean_is_scalar(x_545)) {
 x_560 = lean_alloc_ctor(0, 2, 0);
} else {
 x_560 = x_545;
}
lean_ctor_set(x_560, 0, x_546);
lean_ctor_set(x_560, 1, x_544);
return x_560;
}
}
}
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
lean_dec(x_539);
lean_dec(x_536);
lean_dec(x_535);
lean_dec(x_534);
x_561 = lean_ctor_get(x_542, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_542, 1);
lean_inc(x_562);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 lean_ctor_release(x_542, 1);
 x_563 = x_542;
} else {
 lean_dec_ref(x_542);
 x_563 = lean_box(0);
}
if (lean_is_scalar(x_563)) {
 x_564 = lean_alloc_ctor(1, 2, 0);
} else {
 x_564 = x_563;
}
lean_ctor_set(x_564, 0, x_561);
lean_ctor_set(x_564, 1, x_562);
return x_564;
}
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
lean_dec(x_536);
lean_dec(x_535);
lean_dec(x_534);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_565 = lean_ctor_get(x_538, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_538, 1);
lean_inc(x_566);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 lean_ctor_release(x_538, 1);
 x_567 = x_538;
} else {
 lean_dec_ref(x_538);
 x_567 = lean_box(0);
}
if (lean_is_scalar(x_567)) {
 x_568 = lean_alloc_ctor(1, 2, 0);
} else {
 x_568 = x_567;
}
lean_ctor_set(x_568, 0, x_565);
lean_ctor_set(x_568, 1, x_566);
return x_568;
}
}
case 7:
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; lean_object* x_573; 
x_569 = lean_ctor_get(x_5, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_5, 1);
lean_inc(x_570);
x_571 = lean_ctor_get(x_5, 2);
lean_inc(x_571);
x_572 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_570);
lean_inc(x_1);
x_573 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_570, x_6, x_7, x_8, x_9, x_10, x_11, x_504);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
x_576 = lean_nat_add(x_6, x_265);
lean_dec(x_6);
lean_inc(x_571);
x_577 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_571, x_576, x_7, x_8, x_9, x_10, x_11, x_575);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; size_t x_582; size_t x_583; uint8_t x_584; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 lean_ctor_release(x_577, 1);
 x_580 = x_577;
} else {
 lean_dec_ref(x_577);
 x_580 = lean_box(0);
}
lean_inc(x_571);
lean_inc(x_570);
lean_inc(x_569);
x_581 = l_Lean_Expr_forallE___override(x_569, x_570, x_571, x_572);
x_582 = lean_ptr_addr(x_570);
lean_dec(x_570);
x_583 = lean_ptr_addr(x_574);
x_584 = lean_usize_dec_eq(x_582, x_583);
if (x_584 == 0)
{
lean_object* x_585; lean_object* x_586; 
lean_dec(x_581);
lean_dec(x_571);
x_585 = l_Lean_Expr_forallE___override(x_569, x_574, x_578, x_572);
if (lean_is_scalar(x_580)) {
 x_586 = lean_alloc_ctor(0, 2, 0);
} else {
 x_586 = x_580;
}
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_579);
return x_586;
}
else
{
size_t x_587; size_t x_588; uint8_t x_589; 
x_587 = lean_ptr_addr(x_571);
lean_dec(x_571);
x_588 = lean_ptr_addr(x_578);
x_589 = lean_usize_dec_eq(x_587, x_588);
if (x_589 == 0)
{
lean_object* x_590; lean_object* x_591; 
lean_dec(x_581);
x_590 = l_Lean_Expr_forallE___override(x_569, x_574, x_578, x_572);
if (lean_is_scalar(x_580)) {
 x_591 = lean_alloc_ctor(0, 2, 0);
} else {
 x_591 = x_580;
}
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_579);
return x_591;
}
else
{
uint8_t x_592; 
x_592 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_572, x_572);
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; 
lean_dec(x_581);
x_593 = l_Lean_Expr_forallE___override(x_569, x_574, x_578, x_572);
if (lean_is_scalar(x_580)) {
 x_594 = lean_alloc_ctor(0, 2, 0);
} else {
 x_594 = x_580;
}
lean_ctor_set(x_594, 0, x_593);
lean_ctor_set(x_594, 1, x_579);
return x_594;
}
else
{
lean_object* x_595; 
lean_dec(x_578);
lean_dec(x_574);
lean_dec(x_569);
if (lean_is_scalar(x_580)) {
 x_595 = lean_alloc_ctor(0, 2, 0);
} else {
 x_595 = x_580;
}
lean_ctor_set(x_595, 0, x_581);
lean_ctor_set(x_595, 1, x_579);
return x_595;
}
}
}
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_574);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
x_596 = lean_ctor_get(x_577, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_577, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 lean_ctor_release(x_577, 1);
 x_598 = x_577;
} else {
 lean_dec_ref(x_577);
 x_598 = lean_box(0);
}
if (lean_is_scalar(x_598)) {
 x_599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_599 = x_598;
}
lean_ctor_set(x_599, 0, x_596);
lean_ctor_set(x_599, 1, x_597);
return x_599;
}
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_600 = lean_ctor_get(x_573, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_573, 1);
lean_inc(x_601);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 lean_ctor_release(x_573, 1);
 x_602 = x_573;
} else {
 lean_dec_ref(x_573);
 x_602 = lean_box(0);
}
if (lean_is_scalar(x_602)) {
 x_603 = lean_alloc_ctor(1, 2, 0);
} else {
 x_603 = x_602;
}
lean_ctor_set(x_603, 0, x_600);
lean_ctor_set(x_603, 1, x_601);
return x_603;
}
}
case 8:
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; uint8_t x_608; lean_object* x_609; 
x_604 = lean_ctor_get(x_5, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_5, 1);
lean_inc(x_605);
x_606 = lean_ctor_get(x_5, 2);
lean_inc(x_606);
x_607 = lean_ctor_get(x_5, 3);
lean_inc(x_607);
x_608 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_605);
lean_inc(x_1);
x_609 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_605, x_6, x_7, x_8, x_9, x_10, x_11, x_504);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_610 = lean_ctor_get(x_609, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_609, 1);
lean_inc(x_611);
lean_dec(x_609);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_606);
lean_inc(x_1);
x_612 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_606, x_6, x_7, x_8, x_9, x_10, x_11, x_611);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec(x_612);
x_615 = lean_nat_add(x_6, x_265);
lean_dec(x_6);
lean_inc(x_607);
x_616 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_607, x_615, x_7, x_8, x_9, x_10, x_11, x_614);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; size_t x_620; size_t x_621; uint8_t x_622; 
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 lean_ctor_release(x_616, 1);
 x_619 = x_616;
} else {
 lean_dec_ref(x_616);
 x_619 = lean_box(0);
}
x_620 = lean_ptr_addr(x_605);
lean_dec(x_605);
x_621 = lean_ptr_addr(x_610);
x_622 = lean_usize_dec_eq(x_620, x_621);
if (x_622 == 0)
{
lean_object* x_623; lean_object* x_624; 
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_5);
x_623 = l_Lean_Expr_letE___override(x_604, x_610, x_613, x_617, x_608);
if (lean_is_scalar(x_619)) {
 x_624 = lean_alloc_ctor(0, 2, 0);
} else {
 x_624 = x_619;
}
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_624, 1, x_618);
return x_624;
}
else
{
size_t x_625; size_t x_626; uint8_t x_627; 
x_625 = lean_ptr_addr(x_606);
lean_dec(x_606);
x_626 = lean_ptr_addr(x_613);
x_627 = lean_usize_dec_eq(x_625, x_626);
if (x_627 == 0)
{
lean_object* x_628; lean_object* x_629; 
lean_dec(x_607);
lean_dec(x_5);
x_628 = l_Lean_Expr_letE___override(x_604, x_610, x_613, x_617, x_608);
if (lean_is_scalar(x_619)) {
 x_629 = lean_alloc_ctor(0, 2, 0);
} else {
 x_629 = x_619;
}
lean_ctor_set(x_629, 0, x_628);
lean_ctor_set(x_629, 1, x_618);
return x_629;
}
else
{
size_t x_630; size_t x_631; uint8_t x_632; 
x_630 = lean_ptr_addr(x_607);
lean_dec(x_607);
x_631 = lean_ptr_addr(x_617);
x_632 = lean_usize_dec_eq(x_630, x_631);
if (x_632 == 0)
{
lean_object* x_633; lean_object* x_634; 
lean_dec(x_5);
x_633 = l_Lean_Expr_letE___override(x_604, x_610, x_613, x_617, x_608);
if (lean_is_scalar(x_619)) {
 x_634 = lean_alloc_ctor(0, 2, 0);
} else {
 x_634 = x_619;
}
lean_ctor_set(x_634, 0, x_633);
lean_ctor_set(x_634, 1, x_618);
return x_634;
}
else
{
lean_object* x_635; 
lean_dec(x_617);
lean_dec(x_613);
lean_dec(x_610);
lean_dec(x_604);
if (lean_is_scalar(x_619)) {
 x_635 = lean_alloc_ctor(0, 2, 0);
} else {
 x_635 = x_619;
}
lean_ctor_set(x_635, 0, x_5);
lean_ctor_set(x_635, 1, x_618);
return x_635;
}
}
}
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
lean_dec(x_613);
lean_dec(x_610);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_5);
x_636 = lean_ctor_get(x_616, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_616, 1);
lean_inc(x_637);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 lean_ctor_release(x_616, 1);
 x_638 = x_616;
} else {
 lean_dec_ref(x_616);
 x_638 = lean_box(0);
}
if (lean_is_scalar(x_638)) {
 x_639 = lean_alloc_ctor(1, 2, 0);
} else {
 x_639 = x_638;
}
lean_ctor_set(x_639, 0, x_636);
lean_ctor_set(x_639, 1, x_637);
return x_639;
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_610);
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_640 = lean_ctor_get(x_612, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_612, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_642 = x_612;
} else {
 lean_dec_ref(x_612);
 x_642 = lean_box(0);
}
if (lean_is_scalar(x_642)) {
 x_643 = lean_alloc_ctor(1, 2, 0);
} else {
 x_643 = x_642;
}
lean_ctor_set(x_643, 0, x_640);
lean_ctor_set(x_643, 1, x_641);
return x_643;
}
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
lean_dec(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_644 = lean_ctor_get(x_609, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_609, 1);
lean_inc(x_645);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 x_646 = x_609;
} else {
 lean_dec_ref(x_609);
 x_646 = lean_box(0);
}
if (lean_is_scalar(x_646)) {
 x_647 = lean_alloc_ctor(1, 2, 0);
} else {
 x_647 = x_646;
}
lean_ctor_set(x_647, 0, x_644);
lean_ctor_set(x_647, 1, x_645);
return x_647;
}
}
case 10:
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = lean_ctor_get(x_5, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_5, 1);
lean_inc(x_649);
lean_inc(x_649);
x_650 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_649, x_6, x_7, x_8, x_9, x_10, x_11, x_504);
if (lean_obj_tag(x_650) == 0)
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; size_t x_654; size_t x_655; uint8_t x_656; 
x_651 = lean_ctor_get(x_650, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_650, 1);
lean_inc(x_652);
if (lean_is_exclusive(x_650)) {
 lean_ctor_release(x_650, 0);
 lean_ctor_release(x_650, 1);
 x_653 = x_650;
} else {
 lean_dec_ref(x_650);
 x_653 = lean_box(0);
}
x_654 = lean_ptr_addr(x_649);
lean_dec(x_649);
x_655 = lean_ptr_addr(x_651);
x_656 = lean_usize_dec_eq(x_654, x_655);
if (x_656 == 0)
{
lean_object* x_657; lean_object* x_658; 
lean_dec(x_5);
x_657 = l_Lean_Expr_mdata___override(x_648, x_651);
if (lean_is_scalar(x_653)) {
 x_658 = lean_alloc_ctor(0, 2, 0);
} else {
 x_658 = x_653;
}
lean_ctor_set(x_658, 0, x_657);
lean_ctor_set(x_658, 1, x_652);
return x_658;
}
else
{
lean_object* x_659; 
lean_dec(x_651);
lean_dec(x_648);
if (lean_is_scalar(x_653)) {
 x_659 = lean_alloc_ctor(0, 2, 0);
} else {
 x_659 = x_653;
}
lean_ctor_set(x_659, 0, x_5);
lean_ctor_set(x_659, 1, x_652);
return x_659;
}
}
else
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
lean_dec(x_649);
lean_dec(x_648);
lean_dec(x_5);
x_660 = lean_ctor_get(x_650, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_650, 1);
lean_inc(x_661);
if (lean_is_exclusive(x_650)) {
 lean_ctor_release(x_650, 0);
 lean_ctor_release(x_650, 1);
 x_662 = x_650;
} else {
 lean_dec_ref(x_650);
 x_662 = lean_box(0);
}
if (lean_is_scalar(x_662)) {
 x_663 = lean_alloc_ctor(1, 2, 0);
} else {
 x_663 = x_662;
}
lean_ctor_set(x_663, 0, x_660);
lean_ctor_set(x_663, 1, x_661);
return x_663;
}
}
case 11:
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_664 = lean_ctor_get(x_5, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_5, 1);
lean_inc(x_665);
x_666 = lean_ctor_get(x_5, 2);
lean_inc(x_666);
lean_inc(x_666);
x_667 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_666, x_6, x_7, x_8, x_9, x_10, x_11, x_504);
if (lean_obj_tag(x_667) == 0)
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; size_t x_671; size_t x_672; uint8_t x_673; 
x_668 = lean_ctor_get(x_667, 0);
lean_inc(x_668);
x_669 = lean_ctor_get(x_667, 1);
lean_inc(x_669);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 x_670 = x_667;
} else {
 lean_dec_ref(x_667);
 x_670 = lean_box(0);
}
x_671 = lean_ptr_addr(x_666);
lean_dec(x_666);
x_672 = lean_ptr_addr(x_668);
x_673 = lean_usize_dec_eq(x_671, x_672);
if (x_673 == 0)
{
lean_object* x_674; lean_object* x_675; 
lean_dec(x_5);
x_674 = l_Lean_Expr_proj___override(x_664, x_665, x_668);
if (lean_is_scalar(x_670)) {
 x_675 = lean_alloc_ctor(0, 2, 0);
} else {
 x_675 = x_670;
}
lean_ctor_set(x_675, 0, x_674);
lean_ctor_set(x_675, 1, x_669);
return x_675;
}
else
{
lean_object* x_676; 
lean_dec(x_668);
lean_dec(x_665);
lean_dec(x_664);
if (lean_is_scalar(x_670)) {
 x_676 = lean_alloc_ctor(0, 2, 0);
} else {
 x_676 = x_670;
}
lean_ctor_set(x_676, 0, x_5);
lean_ctor_set(x_676, 1, x_669);
return x_676;
}
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_664);
lean_dec(x_5);
x_677 = lean_ctor_get(x_667, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_667, 1);
lean_inc(x_678);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 x_679 = x_667;
} else {
 lean_dec_ref(x_667);
 x_679 = lean_box(0);
}
if (lean_is_scalar(x_679)) {
 x_680 = lean_alloc_ctor(1, 2, 0);
} else {
 x_680 = x_679;
}
lean_ctor_set(x_680, 0, x_677);
lean_ctor_set(x_680, 1, x_678);
return x_680;
}
}
default: 
{
lean_object* x_681; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_681 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_681, 0, x_5);
lean_ctor_set(x_681, 1, x_504);
return x_681;
}
}
}
else
{
lean_object* x_682; lean_object* x_683; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_682 = l_Lean_Expr_bvar___override(x_6);
x_683 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_683, 0, x_682);
lean_ctor_set(x_683, 1, x_504);
return x_683;
}
}
}
}
else
{
uint8_t x_684; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_684 = !lean_is_exclusive(x_14);
if (x_684 == 0)
{
return x_14;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_685 = lean_ctor_get(x_14, 0);
x_686 = lean_ctor_get(x_14, 1);
lean_inc(x_686);
lean_inc(x_685);
lean_dec(x_14);
x_687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_687, 0, x_685);
lean_ctor_set(x_687, 1, x_686);
return x_687;
}
}
}
else
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_688 = lean_ctor_get(x_5, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_5, 1);
lean_inc(x_689);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_688);
lean_inc(x_1);
x_690 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_688, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
lean_dec(x_690);
lean_inc(x_689);
x_693 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_689, x_6, x_7, x_8, x_9, x_10, x_11, x_692);
if (lean_obj_tag(x_693) == 0)
{
uint8_t x_694; 
x_694 = !lean_is_exclusive(x_693);
if (x_694 == 0)
{
lean_object* x_695; size_t x_696; size_t x_697; uint8_t x_698; 
x_695 = lean_ctor_get(x_693, 0);
x_696 = lean_ptr_addr(x_688);
lean_dec(x_688);
x_697 = lean_ptr_addr(x_691);
x_698 = lean_usize_dec_eq(x_696, x_697);
if (x_698 == 0)
{
lean_object* x_699; 
lean_dec(x_689);
lean_dec(x_5);
x_699 = l_Lean_Expr_app___override(x_691, x_695);
lean_ctor_set(x_693, 0, x_699);
return x_693;
}
else
{
size_t x_700; size_t x_701; uint8_t x_702; 
x_700 = lean_ptr_addr(x_689);
lean_dec(x_689);
x_701 = lean_ptr_addr(x_695);
x_702 = lean_usize_dec_eq(x_700, x_701);
if (x_702 == 0)
{
lean_object* x_703; 
lean_dec(x_5);
x_703 = l_Lean_Expr_app___override(x_691, x_695);
lean_ctor_set(x_693, 0, x_703);
return x_693;
}
else
{
lean_dec(x_695);
lean_dec(x_691);
lean_ctor_set(x_693, 0, x_5);
return x_693;
}
}
}
else
{
lean_object* x_704; lean_object* x_705; size_t x_706; size_t x_707; uint8_t x_708; 
x_704 = lean_ctor_get(x_693, 0);
x_705 = lean_ctor_get(x_693, 1);
lean_inc(x_705);
lean_inc(x_704);
lean_dec(x_693);
x_706 = lean_ptr_addr(x_688);
lean_dec(x_688);
x_707 = lean_ptr_addr(x_691);
x_708 = lean_usize_dec_eq(x_706, x_707);
if (x_708 == 0)
{
lean_object* x_709; lean_object* x_710; 
lean_dec(x_689);
lean_dec(x_5);
x_709 = l_Lean_Expr_app___override(x_691, x_704);
x_710 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_710, 0, x_709);
lean_ctor_set(x_710, 1, x_705);
return x_710;
}
else
{
size_t x_711; size_t x_712; uint8_t x_713; 
x_711 = lean_ptr_addr(x_689);
lean_dec(x_689);
x_712 = lean_ptr_addr(x_704);
x_713 = lean_usize_dec_eq(x_711, x_712);
if (x_713 == 0)
{
lean_object* x_714; lean_object* x_715; 
lean_dec(x_5);
x_714 = l_Lean_Expr_app___override(x_691, x_704);
x_715 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_715, 0, x_714);
lean_ctor_set(x_715, 1, x_705);
return x_715;
}
else
{
lean_object* x_716; 
lean_dec(x_704);
lean_dec(x_691);
x_716 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_716, 0, x_5);
lean_ctor_set(x_716, 1, x_705);
return x_716;
}
}
}
}
else
{
uint8_t x_717; 
lean_dec(x_691);
lean_dec(x_689);
lean_dec(x_688);
lean_dec(x_5);
x_717 = !lean_is_exclusive(x_693);
if (x_717 == 0)
{
return x_693;
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_718 = lean_ctor_get(x_693, 0);
x_719 = lean_ctor_get(x_693, 1);
lean_inc(x_719);
lean_inc(x_718);
lean_dec(x_693);
x_720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_720, 0, x_718);
lean_ctor_set(x_720, 1, x_719);
return x_720;
}
}
}
else
{
uint8_t x_721; 
lean_dec(x_689);
lean_dec(x_688);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_721 = !lean_is_exclusive(x_690);
if (x_721 == 0)
{
return x_690;
}
else
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_722 = lean_ctor_get(x_690, 0);
x_723 = lean_ctor_get(x_690, 1);
lean_inc(x_723);
lean_inc(x_722);
lean_dec(x_690);
x_724 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_724, 0, x_722);
lean_ctor_set(x_724, 1, x_723);
return x_724;
}
}
}
case 6:
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; uint8_t x_728; lean_object* x_729; 
x_725 = lean_ctor_get(x_5, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_5, 1);
lean_inc(x_726);
x_727 = lean_ctor_get(x_5, 2);
lean_inc(x_727);
x_728 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_726);
lean_inc(x_1);
x_729 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_726, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
lean_dec(x_729);
x_732 = lean_unsigned_to_nat(1u);
x_733 = lean_nat_add(x_6, x_732);
lean_dec(x_6);
lean_inc(x_727);
x_734 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_727, x_733, x_7, x_8, x_9, x_10, x_11, x_731);
if (lean_obj_tag(x_734) == 0)
{
uint8_t x_735; 
x_735 = !lean_is_exclusive(x_734);
if (x_735 == 0)
{
lean_object* x_736; lean_object* x_737; size_t x_738; size_t x_739; uint8_t x_740; 
x_736 = lean_ctor_get(x_734, 0);
lean_inc(x_727);
lean_inc(x_726);
lean_inc(x_725);
x_737 = l_Lean_Expr_lam___override(x_725, x_726, x_727, x_728);
x_738 = lean_ptr_addr(x_726);
lean_dec(x_726);
x_739 = lean_ptr_addr(x_730);
x_740 = lean_usize_dec_eq(x_738, x_739);
if (x_740 == 0)
{
lean_object* x_741; 
lean_dec(x_737);
lean_dec(x_727);
x_741 = l_Lean_Expr_lam___override(x_725, x_730, x_736, x_728);
lean_ctor_set(x_734, 0, x_741);
return x_734;
}
else
{
size_t x_742; size_t x_743; uint8_t x_744; 
x_742 = lean_ptr_addr(x_727);
lean_dec(x_727);
x_743 = lean_ptr_addr(x_736);
x_744 = lean_usize_dec_eq(x_742, x_743);
if (x_744 == 0)
{
lean_object* x_745; 
lean_dec(x_737);
x_745 = l_Lean_Expr_lam___override(x_725, x_730, x_736, x_728);
lean_ctor_set(x_734, 0, x_745);
return x_734;
}
else
{
uint8_t x_746; 
x_746 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_728, x_728);
if (x_746 == 0)
{
lean_object* x_747; 
lean_dec(x_737);
x_747 = l_Lean_Expr_lam___override(x_725, x_730, x_736, x_728);
lean_ctor_set(x_734, 0, x_747);
return x_734;
}
else
{
lean_dec(x_736);
lean_dec(x_730);
lean_dec(x_725);
lean_ctor_set(x_734, 0, x_737);
return x_734;
}
}
}
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; size_t x_751; size_t x_752; uint8_t x_753; 
x_748 = lean_ctor_get(x_734, 0);
x_749 = lean_ctor_get(x_734, 1);
lean_inc(x_749);
lean_inc(x_748);
lean_dec(x_734);
lean_inc(x_727);
lean_inc(x_726);
lean_inc(x_725);
x_750 = l_Lean_Expr_lam___override(x_725, x_726, x_727, x_728);
x_751 = lean_ptr_addr(x_726);
lean_dec(x_726);
x_752 = lean_ptr_addr(x_730);
x_753 = lean_usize_dec_eq(x_751, x_752);
if (x_753 == 0)
{
lean_object* x_754; lean_object* x_755; 
lean_dec(x_750);
lean_dec(x_727);
x_754 = l_Lean_Expr_lam___override(x_725, x_730, x_748, x_728);
x_755 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_755, 0, x_754);
lean_ctor_set(x_755, 1, x_749);
return x_755;
}
else
{
size_t x_756; size_t x_757; uint8_t x_758; 
x_756 = lean_ptr_addr(x_727);
lean_dec(x_727);
x_757 = lean_ptr_addr(x_748);
x_758 = lean_usize_dec_eq(x_756, x_757);
if (x_758 == 0)
{
lean_object* x_759; lean_object* x_760; 
lean_dec(x_750);
x_759 = l_Lean_Expr_lam___override(x_725, x_730, x_748, x_728);
x_760 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_760, 0, x_759);
lean_ctor_set(x_760, 1, x_749);
return x_760;
}
else
{
uint8_t x_761; 
x_761 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_728, x_728);
if (x_761 == 0)
{
lean_object* x_762; lean_object* x_763; 
lean_dec(x_750);
x_762 = l_Lean_Expr_lam___override(x_725, x_730, x_748, x_728);
x_763 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_763, 0, x_762);
lean_ctor_set(x_763, 1, x_749);
return x_763;
}
else
{
lean_object* x_764; 
lean_dec(x_748);
lean_dec(x_730);
lean_dec(x_725);
x_764 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_764, 0, x_750);
lean_ctor_set(x_764, 1, x_749);
return x_764;
}
}
}
}
}
else
{
uint8_t x_765; 
lean_dec(x_730);
lean_dec(x_727);
lean_dec(x_726);
lean_dec(x_725);
x_765 = !lean_is_exclusive(x_734);
if (x_765 == 0)
{
return x_734;
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; 
x_766 = lean_ctor_get(x_734, 0);
x_767 = lean_ctor_get(x_734, 1);
lean_inc(x_767);
lean_inc(x_766);
lean_dec(x_734);
x_768 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_768, 0, x_766);
lean_ctor_set(x_768, 1, x_767);
return x_768;
}
}
}
else
{
uint8_t x_769; 
lean_dec(x_727);
lean_dec(x_726);
lean_dec(x_725);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_769 = !lean_is_exclusive(x_729);
if (x_769 == 0)
{
return x_729;
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; 
x_770 = lean_ctor_get(x_729, 0);
x_771 = lean_ctor_get(x_729, 1);
lean_inc(x_771);
lean_inc(x_770);
lean_dec(x_729);
x_772 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_772, 0, x_770);
lean_ctor_set(x_772, 1, x_771);
return x_772;
}
}
}
case 7:
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; uint8_t x_776; lean_object* x_777; 
x_773 = lean_ctor_get(x_5, 0);
lean_inc(x_773);
x_774 = lean_ctor_get(x_5, 1);
lean_inc(x_774);
x_775 = lean_ctor_get(x_5, 2);
lean_inc(x_775);
x_776 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_774);
lean_inc(x_1);
x_777 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_774, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_777) == 0)
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_778 = lean_ctor_get(x_777, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_777, 1);
lean_inc(x_779);
lean_dec(x_777);
x_780 = lean_unsigned_to_nat(1u);
x_781 = lean_nat_add(x_6, x_780);
lean_dec(x_6);
lean_inc(x_775);
x_782 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_775, x_781, x_7, x_8, x_9, x_10, x_11, x_779);
if (lean_obj_tag(x_782) == 0)
{
uint8_t x_783; 
x_783 = !lean_is_exclusive(x_782);
if (x_783 == 0)
{
lean_object* x_784; lean_object* x_785; size_t x_786; size_t x_787; uint8_t x_788; 
x_784 = lean_ctor_get(x_782, 0);
lean_inc(x_775);
lean_inc(x_774);
lean_inc(x_773);
x_785 = l_Lean_Expr_forallE___override(x_773, x_774, x_775, x_776);
x_786 = lean_ptr_addr(x_774);
lean_dec(x_774);
x_787 = lean_ptr_addr(x_778);
x_788 = lean_usize_dec_eq(x_786, x_787);
if (x_788 == 0)
{
lean_object* x_789; 
lean_dec(x_785);
lean_dec(x_775);
x_789 = l_Lean_Expr_forallE___override(x_773, x_778, x_784, x_776);
lean_ctor_set(x_782, 0, x_789);
return x_782;
}
else
{
size_t x_790; size_t x_791; uint8_t x_792; 
x_790 = lean_ptr_addr(x_775);
lean_dec(x_775);
x_791 = lean_ptr_addr(x_784);
x_792 = lean_usize_dec_eq(x_790, x_791);
if (x_792 == 0)
{
lean_object* x_793; 
lean_dec(x_785);
x_793 = l_Lean_Expr_forallE___override(x_773, x_778, x_784, x_776);
lean_ctor_set(x_782, 0, x_793);
return x_782;
}
else
{
uint8_t x_794; 
x_794 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_776, x_776);
if (x_794 == 0)
{
lean_object* x_795; 
lean_dec(x_785);
x_795 = l_Lean_Expr_forallE___override(x_773, x_778, x_784, x_776);
lean_ctor_set(x_782, 0, x_795);
return x_782;
}
else
{
lean_dec(x_784);
lean_dec(x_778);
lean_dec(x_773);
lean_ctor_set(x_782, 0, x_785);
return x_782;
}
}
}
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; size_t x_799; size_t x_800; uint8_t x_801; 
x_796 = lean_ctor_get(x_782, 0);
x_797 = lean_ctor_get(x_782, 1);
lean_inc(x_797);
lean_inc(x_796);
lean_dec(x_782);
lean_inc(x_775);
lean_inc(x_774);
lean_inc(x_773);
x_798 = l_Lean_Expr_forallE___override(x_773, x_774, x_775, x_776);
x_799 = lean_ptr_addr(x_774);
lean_dec(x_774);
x_800 = lean_ptr_addr(x_778);
x_801 = lean_usize_dec_eq(x_799, x_800);
if (x_801 == 0)
{
lean_object* x_802; lean_object* x_803; 
lean_dec(x_798);
lean_dec(x_775);
x_802 = l_Lean_Expr_forallE___override(x_773, x_778, x_796, x_776);
x_803 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_803, 0, x_802);
lean_ctor_set(x_803, 1, x_797);
return x_803;
}
else
{
size_t x_804; size_t x_805; uint8_t x_806; 
x_804 = lean_ptr_addr(x_775);
lean_dec(x_775);
x_805 = lean_ptr_addr(x_796);
x_806 = lean_usize_dec_eq(x_804, x_805);
if (x_806 == 0)
{
lean_object* x_807; lean_object* x_808; 
lean_dec(x_798);
x_807 = l_Lean_Expr_forallE___override(x_773, x_778, x_796, x_776);
x_808 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_808, 0, x_807);
lean_ctor_set(x_808, 1, x_797);
return x_808;
}
else
{
uint8_t x_809; 
x_809 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_776, x_776);
if (x_809 == 0)
{
lean_object* x_810; lean_object* x_811; 
lean_dec(x_798);
x_810 = l_Lean_Expr_forallE___override(x_773, x_778, x_796, x_776);
x_811 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_811, 0, x_810);
lean_ctor_set(x_811, 1, x_797);
return x_811;
}
else
{
lean_object* x_812; 
lean_dec(x_796);
lean_dec(x_778);
lean_dec(x_773);
x_812 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_812, 0, x_798);
lean_ctor_set(x_812, 1, x_797);
return x_812;
}
}
}
}
}
else
{
uint8_t x_813; 
lean_dec(x_778);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
x_813 = !lean_is_exclusive(x_782);
if (x_813 == 0)
{
return x_782;
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_814 = lean_ctor_get(x_782, 0);
x_815 = lean_ctor_get(x_782, 1);
lean_inc(x_815);
lean_inc(x_814);
lean_dec(x_782);
x_816 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_816, 0, x_814);
lean_ctor_set(x_816, 1, x_815);
return x_816;
}
}
}
else
{
uint8_t x_817; 
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_817 = !lean_is_exclusive(x_777);
if (x_817 == 0)
{
return x_777;
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_818 = lean_ctor_get(x_777, 0);
x_819 = lean_ctor_get(x_777, 1);
lean_inc(x_819);
lean_inc(x_818);
lean_dec(x_777);
x_820 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_820, 0, x_818);
lean_ctor_set(x_820, 1, x_819);
return x_820;
}
}
}
case 8:
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; uint8_t x_825; lean_object* x_826; 
x_821 = lean_ctor_get(x_5, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_5, 1);
lean_inc(x_822);
x_823 = lean_ctor_get(x_5, 2);
lean_inc(x_823);
x_824 = lean_ctor_get(x_5, 3);
lean_inc(x_824);
x_825 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_822);
lean_inc(x_1);
x_826 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_822, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_826) == 0)
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; 
x_827 = lean_ctor_get(x_826, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_826, 1);
lean_inc(x_828);
lean_dec(x_826);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_823);
lean_inc(x_1);
x_829 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_823, x_6, x_7, x_8, x_9, x_10, x_11, x_828);
if (lean_obj_tag(x_829) == 0)
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; 
x_830 = lean_ctor_get(x_829, 0);
lean_inc(x_830);
x_831 = lean_ctor_get(x_829, 1);
lean_inc(x_831);
lean_dec(x_829);
x_832 = lean_unsigned_to_nat(1u);
x_833 = lean_nat_add(x_6, x_832);
lean_dec(x_6);
lean_inc(x_824);
x_834 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_824, x_833, x_7, x_8, x_9, x_10, x_11, x_831);
if (lean_obj_tag(x_834) == 0)
{
uint8_t x_835; 
x_835 = !lean_is_exclusive(x_834);
if (x_835 == 0)
{
lean_object* x_836; size_t x_837; size_t x_838; uint8_t x_839; 
x_836 = lean_ctor_get(x_834, 0);
x_837 = lean_ptr_addr(x_822);
lean_dec(x_822);
x_838 = lean_ptr_addr(x_827);
x_839 = lean_usize_dec_eq(x_837, x_838);
if (x_839 == 0)
{
lean_object* x_840; 
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_5);
x_840 = l_Lean_Expr_letE___override(x_821, x_827, x_830, x_836, x_825);
lean_ctor_set(x_834, 0, x_840);
return x_834;
}
else
{
size_t x_841; size_t x_842; uint8_t x_843; 
x_841 = lean_ptr_addr(x_823);
lean_dec(x_823);
x_842 = lean_ptr_addr(x_830);
x_843 = lean_usize_dec_eq(x_841, x_842);
if (x_843 == 0)
{
lean_object* x_844; 
lean_dec(x_824);
lean_dec(x_5);
x_844 = l_Lean_Expr_letE___override(x_821, x_827, x_830, x_836, x_825);
lean_ctor_set(x_834, 0, x_844);
return x_834;
}
else
{
size_t x_845; size_t x_846; uint8_t x_847; 
x_845 = lean_ptr_addr(x_824);
lean_dec(x_824);
x_846 = lean_ptr_addr(x_836);
x_847 = lean_usize_dec_eq(x_845, x_846);
if (x_847 == 0)
{
lean_object* x_848; 
lean_dec(x_5);
x_848 = l_Lean_Expr_letE___override(x_821, x_827, x_830, x_836, x_825);
lean_ctor_set(x_834, 0, x_848);
return x_834;
}
else
{
lean_dec(x_836);
lean_dec(x_830);
lean_dec(x_827);
lean_dec(x_821);
lean_ctor_set(x_834, 0, x_5);
return x_834;
}
}
}
}
else
{
lean_object* x_849; lean_object* x_850; size_t x_851; size_t x_852; uint8_t x_853; 
x_849 = lean_ctor_get(x_834, 0);
x_850 = lean_ctor_get(x_834, 1);
lean_inc(x_850);
lean_inc(x_849);
lean_dec(x_834);
x_851 = lean_ptr_addr(x_822);
lean_dec(x_822);
x_852 = lean_ptr_addr(x_827);
x_853 = lean_usize_dec_eq(x_851, x_852);
if (x_853 == 0)
{
lean_object* x_854; lean_object* x_855; 
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_5);
x_854 = l_Lean_Expr_letE___override(x_821, x_827, x_830, x_849, x_825);
x_855 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_855, 0, x_854);
lean_ctor_set(x_855, 1, x_850);
return x_855;
}
else
{
size_t x_856; size_t x_857; uint8_t x_858; 
x_856 = lean_ptr_addr(x_823);
lean_dec(x_823);
x_857 = lean_ptr_addr(x_830);
x_858 = lean_usize_dec_eq(x_856, x_857);
if (x_858 == 0)
{
lean_object* x_859; lean_object* x_860; 
lean_dec(x_824);
lean_dec(x_5);
x_859 = l_Lean_Expr_letE___override(x_821, x_827, x_830, x_849, x_825);
x_860 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_860, 0, x_859);
lean_ctor_set(x_860, 1, x_850);
return x_860;
}
else
{
size_t x_861; size_t x_862; uint8_t x_863; 
x_861 = lean_ptr_addr(x_824);
lean_dec(x_824);
x_862 = lean_ptr_addr(x_849);
x_863 = lean_usize_dec_eq(x_861, x_862);
if (x_863 == 0)
{
lean_object* x_864; lean_object* x_865; 
lean_dec(x_5);
x_864 = l_Lean_Expr_letE___override(x_821, x_827, x_830, x_849, x_825);
x_865 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_850);
return x_865;
}
else
{
lean_object* x_866; 
lean_dec(x_849);
lean_dec(x_830);
lean_dec(x_827);
lean_dec(x_821);
x_866 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_866, 0, x_5);
lean_ctor_set(x_866, 1, x_850);
return x_866;
}
}
}
}
}
else
{
uint8_t x_867; 
lean_dec(x_830);
lean_dec(x_827);
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_821);
lean_dec(x_5);
x_867 = !lean_is_exclusive(x_834);
if (x_867 == 0)
{
return x_834;
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_868 = lean_ctor_get(x_834, 0);
x_869 = lean_ctor_get(x_834, 1);
lean_inc(x_869);
lean_inc(x_868);
lean_dec(x_834);
x_870 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_870, 0, x_868);
lean_ctor_set(x_870, 1, x_869);
return x_870;
}
}
}
else
{
uint8_t x_871; 
lean_dec(x_827);
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_821);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_871 = !lean_is_exclusive(x_829);
if (x_871 == 0)
{
return x_829;
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_872 = lean_ctor_get(x_829, 0);
x_873 = lean_ctor_get(x_829, 1);
lean_inc(x_873);
lean_inc(x_872);
lean_dec(x_829);
x_874 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_874, 0, x_872);
lean_ctor_set(x_874, 1, x_873);
return x_874;
}
}
}
else
{
uint8_t x_875; 
lean_dec(x_824);
lean_dec(x_823);
lean_dec(x_822);
lean_dec(x_821);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_875 = !lean_is_exclusive(x_826);
if (x_875 == 0)
{
return x_826;
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_876 = lean_ctor_get(x_826, 0);
x_877 = lean_ctor_get(x_826, 1);
lean_inc(x_877);
lean_inc(x_876);
lean_dec(x_826);
x_878 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_878, 0, x_876);
lean_ctor_set(x_878, 1, x_877);
return x_878;
}
}
}
case 10:
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; 
x_879 = lean_ctor_get(x_5, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_5, 1);
lean_inc(x_880);
lean_inc(x_880);
x_881 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_880, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_881) == 0)
{
uint8_t x_882; 
x_882 = !lean_is_exclusive(x_881);
if (x_882 == 0)
{
lean_object* x_883; size_t x_884; size_t x_885; uint8_t x_886; 
x_883 = lean_ctor_get(x_881, 0);
x_884 = lean_ptr_addr(x_880);
lean_dec(x_880);
x_885 = lean_ptr_addr(x_883);
x_886 = lean_usize_dec_eq(x_884, x_885);
if (x_886 == 0)
{
lean_object* x_887; 
lean_dec(x_5);
x_887 = l_Lean_Expr_mdata___override(x_879, x_883);
lean_ctor_set(x_881, 0, x_887);
return x_881;
}
else
{
lean_dec(x_883);
lean_dec(x_879);
lean_ctor_set(x_881, 0, x_5);
return x_881;
}
}
else
{
lean_object* x_888; lean_object* x_889; size_t x_890; size_t x_891; uint8_t x_892; 
x_888 = lean_ctor_get(x_881, 0);
x_889 = lean_ctor_get(x_881, 1);
lean_inc(x_889);
lean_inc(x_888);
lean_dec(x_881);
x_890 = lean_ptr_addr(x_880);
lean_dec(x_880);
x_891 = lean_ptr_addr(x_888);
x_892 = lean_usize_dec_eq(x_890, x_891);
if (x_892 == 0)
{
lean_object* x_893; lean_object* x_894; 
lean_dec(x_5);
x_893 = l_Lean_Expr_mdata___override(x_879, x_888);
x_894 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_894, 0, x_893);
lean_ctor_set(x_894, 1, x_889);
return x_894;
}
else
{
lean_object* x_895; 
lean_dec(x_888);
lean_dec(x_879);
x_895 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_895, 0, x_5);
lean_ctor_set(x_895, 1, x_889);
return x_895;
}
}
}
else
{
uint8_t x_896; 
lean_dec(x_880);
lean_dec(x_879);
lean_dec(x_5);
x_896 = !lean_is_exclusive(x_881);
if (x_896 == 0)
{
return x_881;
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; 
x_897 = lean_ctor_get(x_881, 0);
x_898 = lean_ctor_get(x_881, 1);
lean_inc(x_898);
lean_inc(x_897);
lean_dec(x_881);
x_899 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_899, 0, x_897);
lean_ctor_set(x_899, 1, x_898);
return x_899;
}
}
}
case 11:
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; 
x_900 = lean_ctor_get(x_5, 0);
lean_inc(x_900);
x_901 = lean_ctor_get(x_5, 1);
lean_inc(x_901);
x_902 = lean_ctor_get(x_5, 2);
lean_inc(x_902);
lean_inc(x_902);
x_903 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_902, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_903) == 0)
{
uint8_t x_904; 
x_904 = !lean_is_exclusive(x_903);
if (x_904 == 0)
{
lean_object* x_905; size_t x_906; size_t x_907; uint8_t x_908; 
x_905 = lean_ctor_get(x_903, 0);
x_906 = lean_ptr_addr(x_902);
lean_dec(x_902);
x_907 = lean_ptr_addr(x_905);
x_908 = lean_usize_dec_eq(x_906, x_907);
if (x_908 == 0)
{
lean_object* x_909; 
lean_dec(x_5);
x_909 = l_Lean_Expr_proj___override(x_900, x_901, x_905);
lean_ctor_set(x_903, 0, x_909);
return x_903;
}
else
{
lean_dec(x_905);
lean_dec(x_901);
lean_dec(x_900);
lean_ctor_set(x_903, 0, x_5);
return x_903;
}
}
else
{
lean_object* x_910; lean_object* x_911; size_t x_912; size_t x_913; uint8_t x_914; 
x_910 = lean_ctor_get(x_903, 0);
x_911 = lean_ctor_get(x_903, 1);
lean_inc(x_911);
lean_inc(x_910);
lean_dec(x_903);
x_912 = lean_ptr_addr(x_902);
lean_dec(x_902);
x_913 = lean_ptr_addr(x_910);
x_914 = lean_usize_dec_eq(x_912, x_913);
if (x_914 == 0)
{
lean_object* x_915; lean_object* x_916; 
lean_dec(x_5);
x_915 = l_Lean_Expr_proj___override(x_900, x_901, x_910);
x_916 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_916, 0, x_915);
lean_ctor_set(x_916, 1, x_911);
return x_916;
}
else
{
lean_object* x_917; 
lean_dec(x_910);
lean_dec(x_901);
lean_dec(x_900);
x_917 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_917, 0, x_5);
lean_ctor_set(x_917, 1, x_911);
return x_917;
}
}
}
else
{
uint8_t x_918; 
lean_dec(x_902);
lean_dec(x_901);
lean_dec(x_900);
lean_dec(x_5);
x_918 = !lean_is_exclusive(x_903);
if (x_918 == 0)
{
return x_903;
}
else
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; 
x_919 = lean_ctor_get(x_903, 0);
x_920 = lean_ctor_get(x_903, 1);
lean_inc(x_920);
lean_inc(x_919);
lean_dec(x_903);
x_921 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_921, 0, x_919);
lean_ctor_set(x_921, 1, x_920);
return x_921;
}
}
}
default: 
{
lean_object* x_922; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_922 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_922, 0, x_5);
lean_ctor_set(x_922, 1, x_12);
return x_922;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_kabstract___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Expr_isFVar(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_9);
lean_inc(x_2);
x_14 = l_Lean_Expr_toHeadIndex(x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Expr_headNumArgs_go(x_2, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_st_mk_ref(x_17, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_14, x_16, x_11, x_15, x_19, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_16);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_19, x_23);
lean_dec(x_19);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_19);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_box(0);
x_34 = l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_32_(x_3, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_9);
lean_inc(x_2);
x_35 = l_Lean_Expr_toHeadIndex(x_2);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Expr_headNumArgs_go(x_2, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_st_mk_ref(x_38, x_12);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_35, x_37, x_11, x_36, x_40, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_37);
lean_dec(x_35);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_st_ref_get(x_40, x_44);
lean_dec(x_40);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_40);
x_50 = !lean_is_exclusive(x_42);
if (x_50 == 0)
{
return x_42;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_42, 0);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_42);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_54 = l_Lean_Meta_kabstract___closed__1;
x_55 = lean_array_push(x_54, x_2);
x_56 = lean_expr_abstract(x_11, x_55);
lean_dec(x_55);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_56);
return x_9;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_9, 0);
x_58 = lean_ctor_get(x_9, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_9);
x_59 = l_Lean_Expr_isFVar(x_2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_inc(x_2);
x_60 = l_Lean_Expr_toHeadIndex(x_2);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_Expr_headNumArgs_go(x_2, x_61);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_st_mk_ref(x_63, x_58);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_60, x_62, x_57, x_61, x_65, x_4, x_5, x_6, x_7, x_66);
lean_dec(x_62);
lean_dec(x_60);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_st_ref_get(x_65, x_69);
lean_dec(x_65);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_65);
x_74 = lean_ctor_get(x_67, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_67, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_76 = x_67;
} else {
 lean_dec_ref(x_67);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_box(0);
x_79 = l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_32_(x_3, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_inc(x_2);
x_80 = l_Lean_Expr_toHeadIndex(x_2);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Lean_Expr_headNumArgs_go(x_2, x_81);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_st_mk_ref(x_83, x_58);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_80, x_82, x_57, x_81, x_85, x_4, x_5, x_6, x_7, x_86);
lean_dec(x_82);
lean_dec(x_80);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_st_ref_get(x_85, x_89);
lean_dec(x_85);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_88);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_85);
x_94 = lean_ctor_get(x_87, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_87, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_96 = x_87;
} else {
 lean_dec_ref(x_87);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_98 = l_Lean_Meta_kabstract___closed__1;
x_99 = lean_array_push(x_98, x_2);
x_100 = lean_expr_abstract(x_57, x_99);
lean_dec(x_99);
lean_dec(x_57);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_58);
return x_101;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_kabstract(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Occurrences(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_HeadIndex(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Occurrences(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_HeadIndex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_kabstract___closed__1 = _init_l_Lean_Meta_kabstract___closed__1();
lean_mark_persistent(l_Lean_Meta_kabstract___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
