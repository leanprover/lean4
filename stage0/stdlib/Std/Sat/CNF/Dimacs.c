// Lean compiler output
// Module: Std.Sat.CNF.Dimacs
// Imports: public import Std.Sat.CNF.RelabelFin
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_byte_array_uget(lean_object*, size_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_incrementClauses(lean_object*);
static const lean_string_object l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___closed__0 = (const lean_object*)&l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___closed__0 = (const lean_object*)&l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Std_Sat_CNF_dimacs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Sat_CNF_dimacs___closed__0 = (const lean_object*)&l_Std_Sat_CNF_dimacs___closed__0_value;
static const lean_string_object l_Std_Sat_CNF_dimacs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "p cnf "};
static const lean_object* l_Std_Sat_CNF_dimacs___closed__1 = (const lean_object*)&l_Std_Sat_CNF_dimacs___closed__1_value;
static const lean_string_object l_Std_Sat_CNF_dimacs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Std_Sat_CNF_dimacs___closed__2 = (const lean_object*)&l_Std_Sat_CNF_dimacs___closed__2_value;
static const lean_string_object l_Std_Sat_CNF_dimacs___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Std_Sat_CNF_dimacs___closed__3 = (const lean_object*)&l_Std_Sat_CNF_dimacs___closed__3_value;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit(lean_object* v_lit_1_, lean_object* v_a_2_){
_start:
{
lean_object* v_numClauses_3_; lean_object* v_maxLit_4_; lean_object* v_fst_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_26_; 
v_numClauses_3_ = lean_ctor_get(v_a_2_, 0);
v_maxLit_4_ = lean_ctor_get(v_a_2_, 1);
v_fst_5_ = lean_ctor_get(v_lit_1_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v_lit_1_);
if (v_isSharedCheck_26_ == 0)
{
lean_object* v_unused_27_; 
v_unused_27_ = lean_ctor_get(v_lit_1_, 1);
lean_dec(v_unused_27_);
v___x_7_ = v_lit_1_;
v_isShared_8_ = v_isSharedCheck_26_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_fst_5_);
lean_dec(v_lit_1_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_26_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = lean_box(0);
v___x_10_ = lean_nat_dec_le(v_maxLit_4_, v_fst_5_);
if (v___x_10_ == 0)
{
lean_object* v___x_12_; 
lean_dec(v_fst_5_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_a_2_);
lean_ctor_set(v___x_7_, 0, v___x_9_);
v___x_12_ = v___x_7_;
goto v_reusejp_11_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v___x_9_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v_a_2_);
v___x_12_ = v_reuseFailAlloc_13_;
goto v_reusejp_11_;
}
v_reusejp_11_:
{
return v___x_12_;
}
}
else
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
lean_inc(v_numClauses_3_);
v_isSharedCheck_23_ = !lean_is_exclusive(v_a_2_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; lean_object* v_unused_25_; 
v_unused_24_ = lean_ctor_get(v_a_2_, 1);
lean_dec(v_unused_24_);
v_unused_25_ = lean_ctor_get(v_a_2_, 0);
lean_dec(v_unused_25_);
v___x_15_ = v_a_2_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v_a_2_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 1, v_fst_5_);
v___x_18_ = v___x_15_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_numClauses_3_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_fst_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v___x_18_);
lean_ctor_set(v___x_7_, 0, v___x_9_);
v___x_20_ = v___x_7_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_9_);
lean_ctor_set(v_reuseFailAlloc_21_, 1, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_incrementClauses(lean_object* v_a_28_){
_start:
{
lean_object* v_numClauses_29_; lean_object* v_maxLit_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_41_; 
v_numClauses_29_ = lean_ctor_get(v_a_28_, 0);
v_maxLit_30_ = lean_ctor_get(v_a_28_, 1);
v_isSharedCheck_41_ = !lean_is_exclusive(v_a_28_);
if (v_isSharedCheck_41_ == 0)
{
v___x_32_ = v_a_28_;
v_isShared_33_ = v_isSharedCheck_41_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_maxLit_30_);
lean_inc(v_numClauses_29_);
lean_dec(v_a_28_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_41_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_38_; 
v___x_34_ = lean_box(0);
v___x_35_ = lean_unsigned_to_nat(1u);
v___x_36_ = lean_nat_add(v_numClauses_29_, v___x_35_);
lean_dec(v_numClauses_29_);
if (v_isShared_33_ == 0)
{
lean_ctor_set(v___x_32_, 0, v___x_36_);
v___x_38_ = v___x_32_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v___x_36_);
lean_ctor_set(v_reuseFailAlloc_40_, 1, v_maxLit_30_);
v___x_38_ = v_reuseFailAlloc_40_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
lean_object* v___x_39_; 
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_34_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
return v___x_39_;
}
}
}
}
lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0(lean_object* v_c_43_, size_t v_sz_44_, size_t v_i_45_, lean_object* v_b_46_, lean_object* v___y_47_){
_start:
{
lean_object* v___y_49_; lean_object* v___y_50_; uint8_t v___x_57_; 
v___x_57_ = lean_usize_dec_lt(v_i_45_, v_sz_44_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; 
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v_b_46_);
lean_ctor_set(v___x_58_, 1, v___y_47_);
return v___x_58_;
}
else
{
lean_object* v_atoms_59_; lean_object* v_polarities_60_; lean_object* v_numClauses_61_; lean_object* v_maxLit_62_; lean_object* v___x_63_; uint8_t v___x_64_; uint8_t v___x_65_; uint8_t v___x_66_; lean_object* v_snd_68_; uint8_t v___x_77_; 
v_atoms_59_ = lean_ctor_get(v_c_43_, 0);
v_polarities_60_ = lean_ctor_get(v_c_43_, 1);
v_numClauses_61_ = lean_ctor_get(v___y_47_, 0);
v_maxLit_62_ = lean_ctor_get(v___y_47_, 1);
v___x_63_ = lean_array_uget_borrowed(v_atoms_59_, v_i_45_);
v___x_64_ = lean_byte_array_uget(v_polarities_60_, v_i_45_);
v___x_65_ = 1;
v___x_66_ = lean_uint8_dec_eq(v___x_64_, v___x_65_);
v___x_77_ = lean_nat_dec_le(v_maxLit_62_, v___x_63_);
if (v___x_77_ == 0)
{
v_snd_68_ = v___y_47_;
goto v___jp_67_;
}
else
{
lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
lean_inc(v_numClauses_61_);
v_isSharedCheck_84_ = !lean_is_exclusive(v___y_47_);
if (v_isSharedCheck_84_ == 0)
{
lean_object* v_unused_85_; lean_object* v_unused_86_; 
v_unused_85_ = lean_ctor_get(v___y_47_, 1);
lean_dec(v_unused_85_);
v_unused_86_ = lean_ctor_get(v___y_47_, 0);
lean_dec(v_unused_86_);
v___x_79_ = v___y_47_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_dec(v___y_47_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
lean_inc(v___x_63_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 1, v___x_63_);
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_numClauses_61_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_63_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
v_snd_68_ = v___x_82_;
goto v___jp_67_;
}
}
}
v___jp_67_:
{
if (v___x_66_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_69_ = ((lean_object*)(l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___closed__0));
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_nat_add(v___x_63_, v___x_70_);
v___x_72_ = l_Nat_reprFast(v___x_71_);
v___x_73_ = lean_string_append(v___x_69_, v___x_72_);
lean_dec_ref(v___x_72_);
v___y_49_ = v_snd_68_;
v___y_50_ = v___x_73_;
goto v___jp_48_;
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = lean_unsigned_to_nat(1u);
v___x_75_ = lean_nat_add(v___x_63_, v___x_74_);
v___x_76_ = l_Nat_reprFast(v___x_75_);
v___y_49_ = v_snd_68_;
v___y_50_ = v___x_76_;
goto v___jp_48_;
}
}
}
v___jp_48_:
{
lean_object* v___x_51_; uint32_t v___x_52_; lean_object* v___x_53_; size_t v___x_54_; size_t v___x_55_; 
v___x_51_ = lean_string_append(v_b_46_, v___y_50_);
lean_dec_ref(v___y_50_);
v___x_52_ = 32;
v___x_53_ = lean_string_push(v___x_51_, v___x_52_);
v___x_54_ = ((size_t)1ULL);
v___x_55_ = lean_usize_add(v_i_45_, v___x_54_);
v_i_45_ = v___x_55_;
v_b_46_ = v___x_53_;
v___y_47_ = v___y_49_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_43_ = stack[0].m_obj;
size_t v_sz_44_ = stack[1].m_num;
size_t v_i_45_ = stack[2].m_num;
lean_object* v_b_46_ = stack[3].m_obj;
lean_object* v___y_47_ = stack[4].m_obj;
lean_object* v_res_87_;
v_res_87_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0(v_c_43_, v_sz_44_, v_i_45_, v_b_46_, v___y_47_);
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0___boxed(lean_object* v_c_88_, lean_object* v_sz_89_, lean_object* v_i_90_, lean_object* v_b_91_, lean_object* v___y_92_){
_start:
{
size_t v_sz_boxed_93_; size_t v_i_boxed_94_; lean_object* v_res_95_; 
v_sz_boxed_93_ = lean_unbox_usize(v_sz_89_);
lean_dec(v_sz_89_);
v_i_boxed_94_ = lean_unbox_usize(v_i_90_);
lean_dec(v_i_90_);
v_res_95_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0(v_c_88_, v_sz_boxed_93_, v_i_boxed_94_, v_b_91_, v___y_92_);
lean_dec_ref(v_c_88_);
return v_res_95_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1(lean_object* v_as_96_, size_t v_i_97_, size_t v_stop_98_, lean_object* v_b_99_, lean_object* v___y_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lean_usize_dec_eq(v_i_97_, v_stop_98_);
if (v___x_101_ == 0)
{
lean_object* v_numClauses_102_; lean_object* v_maxLit_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_126_; 
v_numClauses_102_ = lean_ctor_get(v___y_100_, 0);
v_maxLit_103_ = lean_ctor_get(v___y_100_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v___y_100_);
if (v_isSharedCheck_126_ == 0)
{
v___x_105_ = v___y_100_;
v_isShared_106_ = v_isSharedCheck_126_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_maxLit_103_);
lean_inc(v_numClauses_102_);
lean_dec(v___y_100_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_126_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v_atoms_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_107_ = lean_array_uget_borrowed(v_as_96_, v_i_97_);
v_atoms_108_ = lean_ctor_get(v___x_107_, 0);
v___x_109_ = lean_unsigned_to_nat(1u);
v___x_110_ = lean_nat_add(v_numClauses_102_, v___x_109_);
lean_dec(v_numClauses_102_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_110_);
v___x_112_ = v___x_105_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_maxLit_103_);
v___x_112_ = v_reuseFailAlloc_125_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
size_t v_sz_113_; size_t v___x_114_; lean_object* v___x_115_; lean_object* v_fst_116_; lean_object* v_snd_117_; uint32_t v___x_118_; lean_object* v___x_119_; uint32_t v___x_120_; lean_object* v___x_121_; size_t v___x_122_; size_t v___x_123_; 
v_sz_113_ = lean_array_size(v_atoms_108_);
v___x_114_ = ((size_t)0ULL);
v___x_115_ = l___private_Std_Sat_CNF_Basic_0__Std_Sat_CNF_Clause_forIn_x27ImplUnsafe_loop___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__0(v___x_107_, v_sz_113_, v___x_114_, v_b_99_, v___x_112_);
v_fst_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_fst_116_);
v_snd_117_ = lean_ctor_get(v___x_115_, 1);
lean_inc(v_snd_117_);
lean_dec_ref(v___x_115_);
v___x_118_ = 48;
v___x_119_ = lean_string_push(v_fst_116_, v___x_118_);
v___x_120_ = 10;
v___x_121_ = lean_string_push(v___x_119_, v___x_120_);
v___x_122_ = ((size_t)1ULL);
v___x_123_ = lean_usize_add(v_i_97_, v___x_122_);
v_i_97_ = v___x_123_;
v_b_99_ = v___x_121_;
v___y_100_ = v_snd_117_;
goto _start;
}
}
}
else
{
lean_object* v___x_127_; 
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v_b_99_);
lean_ctor_set(v___x_127_, 1, v___y_100_);
return v___x_127_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_96_ = stack[0].m_obj;
size_t v_i_97_ = stack[1].m_num;
size_t v_stop_98_ = stack[2].m_num;
lean_object* v_b_99_ = stack[3].m_obj;
lean_object* v___y_100_ = stack[4].m_obj;
lean_object* v_res_128_;
v_res_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1(v_as_96_, v_i_97_, v_stop_98_, v_b_99_, v___y_100_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1___boxed(lean_object* v_as_129_, lean_object* v_i_130_, lean_object* v_stop_131_, lean_object* v_b_132_, lean_object* v___y_133_){
_start:
{
size_t v_i_boxed_134_; size_t v_stop_boxed_135_; lean_object* v_res_136_; 
v_i_boxed_134_ = lean_unbox_usize(v_i_130_);
lean_dec(v_i_130_);
v_stop_boxed_135_ = lean_unbox_usize(v_stop_131_);
lean_dec(v_stop_131_);
v_res_136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1(v_as_129_, v_i_boxed_134_, v_stop_boxed_135_, v_b_132_, v___y_133_);
lean_dec_ref(v_as_129_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go(lean_object* v_cnf_138_, lean_object* v_a_139_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_140_ = ((lean_object*)(l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___closed__0));
v___x_141_ = lean_unsigned_to_nat(0u);
v___x_142_ = lean_array_get_size(v_cnf_138_);
v___x_143_ = lean_nat_dec_lt(v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; 
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_140_);
lean_ctor_set(v___x_144_, 1, v_a_139_);
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = lean_nat_dec_le(v___x_142_, v___x_142_);
if (v___x_145_ == 0)
{
if (v___x_143_ == 0)
{
lean_object* v___x_146_; 
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_140_);
lean_ctor_set(v___x_146_, 1, v_a_139_);
return v___x_146_;
}
else
{
size_t v___x_147_; size_t v___x_148_; lean_object* v___x_149_; 
v___x_147_ = ((size_t)0ULL);
v___x_148_ = lean_usize_of_nat(v___x_142_);
v___x_149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1(v_cnf_138_, v___x_147_, v___x_148_, v___x_140_, v_a_139_);
return v___x_149_;
}
}
else
{
size_t v___x_150_; size_t v___x_151_; lean_object* v___x_152_; 
v___x_150_ = ((size_t)0ULL);
v___x_151_ = lean_usize_of_nat(v___x_142_);
v___x_152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go_spec__1(v_cnf_138_, v___x_150_, v___x_151_, v___x_140_, v_a_139_);
return v___x_152_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go___boxed(lean_object* v_cnf_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go(v_cnf_153_, v_a_154_);
lean_dec_ref(v_cnf_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs(lean_object* v_cnf_161_){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v_snd_164_; lean_object* v_fst_165_; lean_object* v_numClauses_166_; lean_object* v_maxLit_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_162_ = ((lean_object*)(l_Std_Sat_CNF_dimacs___closed__0));
v___x_163_ = l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_dimacs_go(v_cnf_161_, v___x_162_);
v_snd_164_ = lean_ctor_get(v___x_163_, 1);
lean_inc(v_snd_164_);
v_fst_165_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_fst_165_);
lean_dec_ref(v___x_163_);
v_numClauses_166_ = lean_ctor_get(v_snd_164_, 0);
lean_inc(v_numClauses_166_);
v_maxLit_167_ = lean_ctor_get(v_snd_164_, 1);
lean_inc(v_maxLit_167_);
lean_dec(v_snd_164_);
v___x_168_ = ((lean_object*)(l_Std_Sat_CNF_dimacs___closed__1));
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = lean_nat_add(v_maxLit_167_, v___x_169_);
lean_dec(v_maxLit_167_);
v___x_171_ = l_Nat_reprFast(v___x_170_);
v___x_172_ = lean_string_append(v___x_168_, v___x_171_);
lean_dec_ref(v___x_171_);
v___x_173_ = ((lean_object*)(l_Std_Sat_CNF_dimacs___closed__2));
v___x_174_ = lean_string_append(v___x_172_, v___x_173_);
v___x_175_ = l_Nat_reprFast(v_numClauses_166_);
v___x_176_ = lean_string_append(v___x_174_, v___x_175_);
lean_dec_ref(v___x_175_);
v___x_177_ = ((lean_object*)(l_Std_Sat_CNF_dimacs___closed__3));
v___x_178_ = lean_string_append(v___x_176_, v___x_177_);
v___x_179_ = lean_string_append(v___x_178_, v_fst_165_);
lean_dec(v_fst_165_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs___boxed(lean_object* v_cnf_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Std_Sat_CNF_dimacs(v_cnf_180_);
lean_dec_ref(v_cnf_180_);
return v_res_181_;
}
}
lean_object* runtime_initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_CNF_Dimacs(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Sat_CNF_RelabelFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_CNF_Dimacs(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Dimacs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_RelabelFin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_CNF_Dimacs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_CNF_Dimacs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_CNF_Dimacs(builtin);
}
#ifdef __cplusplus
}
#endif
