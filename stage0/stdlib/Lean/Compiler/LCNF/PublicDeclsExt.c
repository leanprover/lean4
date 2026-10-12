// Lean compiler output
// Module: Lean.Compiler.LCNF.PublicDeclsExt
// Imports: public import Lean.Environment
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
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l___private_Lean_Environment_0__Lean_takeNewEntriesRevUnsafe___redArg(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__0_value)}};
static const lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3 = (const lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__4_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Compiler"};
static const lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__5_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "LCNF"};
static const lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__6 = (const lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__6_value;
static const lean_string_object l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "mkOrderedDeclSetExt"};
static const lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__7_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__8_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__5_value),LEAN_SCALAR_PTR_LITERAL(68, 195, 72, 11, 109, 136, 143, 118)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__8_value_aux_1),((lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__6_value),LEAN_SCALAR_PTR_LITERAL(229, 76, 245, 57, 5, 8, 44, 184)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__8_value_aux_2),((lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__7_value),LEAN_SCALAR_PTR_LITERAL(242, 189, 115, 64, 95, 206, 45, 68)}};
static const lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__8 = (const lean_object*)&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt;
static const lean_ctor_object l_Lean_Compiler_LCNF_isDeclPublic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_isDeclPublic___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_isDeclPublic___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_isDeclPublic___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "_boxed"};
static const lean_object* l_Lean_Compiler_LCNF_isDeclPublic___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_isDeclPublic___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_isDeclPublic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isDeclPublic___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclPublic___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0(lean_object* v_newState_1_, lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_3_) == 0)
{
return v_x_2_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_33_; 
v_head_4_ = lean_ctor_get(v_x_3_, 0);
v_tail_5_ = lean_ctor_get(v_x_3_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_33_ == 0)
{
v___x_7_ = v_x_3_;
v_isShared_8_ = v_isSharedCheck_33_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_tail_5_);
lean_inc(v_head_4_);
lean_dec(v_x_3_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_33_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v_fst_9_; lean_object* v_snd_10_; uint8_t v___x_11_; 
v_fst_9_ = lean_ctor_get(v_x_2_, 0);
v_snd_10_ = lean_ctor_get(v_x_2_, 1);
v___x_11_ = l_Lean_NameSet_contains(v_snd_10_, v_head_4_);
if (v___x_11_ == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_29_; 
lean_inc(v_snd_10_);
lean_inc(v_fst_9_);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_2_);
if (v_isSharedCheck_29_ == 0)
{
lean_object* v_unused_30_; lean_object* v_unused_31_; 
v_unused_30_ = lean_ctor_get(v_x_2_, 1);
lean_dec(v_unused_30_);
v_unused_31_ = lean_ctor_get(v_x_2_, 0);
lean_dec(v_unused_31_);
v___x_13_ = v_x_2_;
v_isShared_14_ = v_isSharedCheck_29_;
goto v_resetjp_12_;
}
else
{
lean_dec(v_x_2_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_29_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v_snd_15_; lean_object* v___x_17_; 
v_snd_15_ = lean_ctor_get(v_newState_1_, 1);
lean_inc(v_head_4_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v_fst_9_);
v___x_17_ = v___x_7_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_head_4_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v_fst_9_);
v___x_17_ = v_reuseFailAlloc_28_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
uint8_t v___x_18_; 
v___x_18_ = l_Lean_NameSet_contains(v_snd_15_, v_head_4_);
if (v___x_18_ == 0)
{
lean_object* v___x_20_; 
lean_dec(v_head_4_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_17_);
v___x_20_ = v___x_13_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_snd_10_);
v___x_20_ = v_reuseFailAlloc_22_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
v_x_2_ = v___x_20_;
v_x_3_ = v_tail_5_;
goto _start;
}
}
else
{
lean_object* v___x_23_; lean_object* v___x_25_; 
v___x_23_ = l_Lean_NameSet_insert(v_snd_10_, v_head_4_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 1, v___x_23_);
lean_ctor_set(v___x_13_, 0, v___x_17_);
v___x_25_ = v___x_13_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v___x_17_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v___x_23_);
v___x_25_ = v_reuseFailAlloc_27_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
v_x_2_ = v___x_25_;
v_x_3_ = v_tail_5_;
goto _start;
}
}
}
}
}
else
{
lean_del_object(v___x_7_);
lean_dec(v_head_4_);
v_x_3_ = v_tail_5_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0___boxed(lean_object* v_newState_34_, lean_object* v_x_35_, lean_object* v_x_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0(v_newState_34_, v_x_35_, v_x_36_);
lean_dec_ref(v_newState_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0(lean_object* v_oldState_38_, lean_object* v_newState_39_, lean_object* v_x_40_, lean_object* v_s_41_){
_start:
{
lean_object* v_fst_42_; lean_object* v_fst_43_; lean_object* v_newEntries_44_; lean_object* v___x_45_; 
v_fst_42_ = lean_ctor_get(v_newState_39_, 0);
v_fst_43_ = lean_ctor_get(v_oldState_38_, 0);
lean_inc(v_fst_42_);
v_newEntries_44_ = l___private_Lean_Environment_0__Lean_takeNewEntriesRevUnsafe___redArg(v_fst_42_, v_fst_43_);
v___x_45_ = l_List_foldl___at___00Lean_Compiler_LCNF_mkOrderedDeclSetExt_spec__0(v_newState_39_, v_s_41_, v_newEntries_44_);
lean_dec_ref(v_newState_39_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0___boxed(lean_object* v_oldState_46_, lean_object* v_newState_47_, lean_object* v_x_48_, lean_object* v_s_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__0(v_oldState_46_, v_newState_47_, v_x_48_, v_s_49_);
lean_dec(v_x_48_);
lean_dec_ref(v_oldState_46_);
return v_res_50_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1(lean_object* v___x_51_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_53_, 0, v___x_51_);
return v___x_53_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_51_ = stack[0].m_obj;
lean_object* v_res_54_;
v_res_54_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1(v___x_51_);
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1___boxed(lean_object* v___x_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1(v___x_55_);
return v_res_57_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = l_Lean_NameSet_empty;
v___x_60_ = lean_box(0);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2(void){
_start:
{
lean_object* v___x_62_; lean_object* v___f_63_; 
v___x_62_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1, &l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1_once, _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__1);
v___f_63_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___lam__1___boxed), 2, 1);
lean_closure_set(v___f_63_, 0, v___x_62_);
return v___f_63_;
}
}
lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt(){
_start:
{
lean_object* v___f_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; 
v___f_76_ = lean_obj_once(&l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2, &l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2_once, _init_l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__2);
v___x_77_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__3));
v___x_78_ = lean_box(0);
v___x_79_ = ((lean_object*)(l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___closed__8));
v___x_80_ = 0;
v___x_81_ = l_Lean_registerEnvExtension___redArg(v___f_76_, v___x_77_, v___x_78_, v___x_79_, v___x_80_, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_mkOrderedDeclSetExt_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_82_;
v_res_82_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
stack->m_obj
 = v_res_82_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_mkOrderedDeclSetExt___boxed(lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
return v_res_84_;
}
}
lean_object* l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_Compiler_LCNF_mkOrderedDeclSetExt();
return v___x_86_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_87_;
v_res_87_ = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2_();
stack->m_obj
 = v_res_87_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2____boxed(lean_object* v_a_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2_();
return v_res_89_;
}
}
uint8_t l_Lean_Compiler_LCNF_isDeclPublic(lean_object* v_env_94_, lean_object* v_declName_95_){
_start:
{
lean_object* v___x_96_; uint8_t v_isModule_97_; 
v___x_96_ = l_Lean_Environment_header(v_env_94_);
v_isModule_97_ = lean_ctor_get_uint8(v___x_96_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_96_);
if (v_isModule_97_ == 0)
{
uint8_t v___x_98_; 
lean_dec_ref(v_env_94_);
v___x_98_ = 1;
return v___x_98_;
}
else
{
lean_object* v___x_99_; uint8_t v___x_100_; lean_object* v___y_102_; 
v___x_99_ = ((lean_object*)(l_Lean_Compiler_LCNF_isDeclPublic___closed__0));
v___x_100_ = 0;
if (lean_obj_tag(v_declName_95_) == 1)
{
lean_object* v_pre_109_; lean_object* v_str_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v_pre_109_ = lean_ctor_get(v_declName_95_, 0);
v_str_110_ = lean_ctor_get(v_declName_95_, 1);
v___x_111_ = ((lean_object*)(l_Lean_Compiler_LCNF_isDeclPublic___closed__1));
v___x_112_ = lean_string_dec_eq(v_str_110_, v___x_111_);
if (v___x_112_ == 0)
{
v___y_102_ = v_declName_95_;
goto v___jp_101_;
}
else
{
v___y_102_ = v_pre_109_;
goto v___jp_101_;
}
}
else
{
v___y_102_ = v_declName_95_;
goto v___jp_101_;
}
v___jp_101_:
{
lean_object* v___x_103_; lean_object* v_asyncMode_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v_snd_107_; uint8_t v___x_108_; 
v___x_103_ = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt;
v_asyncMode_104_ = lean_ctor_get(v___x_103_, 2);
v___x_105_ = lean_box(0);
v___x_106_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_99_, v___x_103_, v_env_94_, v_asyncMode_104_, v___x_105_, v___x_100_);
v_snd_107_ = lean_ctor_get(v___x_106_, 1);
lean_inc(v_snd_107_);
lean_dec(v___x_106_);
v___x_108_ = l_Lean_NameSet_contains(v_snd_107_, v___y_102_);
lean_dec(v_snd_107_);
return v___x_108_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_isDeclPublic_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_94_ = stack[0].m_obj;
lean_object* v_declName_95_ = stack[1].m_obj;
uint8_t v_res_113_;
v_res_113_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_94_, v_declName_95_);
stack->m_num = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_isDeclPublic___boxed(lean_object* v_env_114_, lean_object* v_declName_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_114_, v_declName_115_);
lean_dec(v_declName_115_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclPublic___lam__0(lean_object* v_declName_118_, lean_object* v_s_119_){
_start:
{
lean_object* v_fst_120_; lean_object* v_snd_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_130_; 
v_fst_120_ = lean_ctor_get(v_s_119_, 0);
v_snd_121_ = lean_ctor_get(v_s_119_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_s_119_);
if (v_isSharedCheck_130_ == 0)
{
v___x_123_ = v_s_119_;
v_isShared_124_ = v_isSharedCheck_130_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_snd_121_);
lean_inc(v_fst_120_);
lean_dec(v_s_119_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_130_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
lean_inc(v_declName_118_);
v___x_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_125_, 0, v_declName_118_);
lean_ctor_set(v___x_125_, 1, v_fst_120_);
v___x_126_ = l_Lean_NameSet_insert(v_snd_121_, v_declName_118_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___x_126_);
lean_ctor_set(v___x_123_, 0, v___x_125_);
v___x_128_ = v___x_123_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_125_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object* v_env_131_, lean_object* v_declName_132_){
_start:
{
uint8_t v___x_133_; 
lean_inc_ref(v_env_131_);
v___x_133_ = l_Lean_Compiler_LCNF_isDeclPublic(v_env_131_, v_declName_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v_asyncMode_135_; uint8_t v_logWrites_136_; lean_object* v___f_137_; uint8_t v___x_138_; lean_object* v___x_139_; 
v___x_134_ = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt;
v_asyncMode_135_ = lean_ctor_get(v___x_134_, 2);
v_logWrites_136_ = lean_ctor_get_uint8(v___x_134_, sizeof(void*)*6);
v___f_137_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_setDeclPublic___lam__0), 2, 1);
lean_closure_set(v___f_137_, 0, v_declName_132_);
v___x_138_ = 1;
v___x_139_ = lean_box(0);
if (v_logWrites_136_ == 0)
{
lean_object* v___x_140_; 
v___x_140_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_134_, v_env_131_, v___f_137_, v_asyncMode_135_, v___x_139_, v___x_138_);
return v___x_140_;
}
else
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_134_, v_env_131_);
lean_dec_ref(v_env_131_);
v___x_142_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_134_, v___x_141_, v___f_137_, v_asyncMode_135_, v___x_139_, v___x_138_);
return v___x_142_;
}
}
else
{
lean_dec(v_declName_132_);
return v_env_131_;
}
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_PublicDeclsExt_3962556520____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Compiler_LCNF_PublicDeclsExt_0__Lean_Compiler_LCNF_publicDeclsExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_PublicDeclsExt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_PublicDeclsExt(builtin);
}
#ifdef __cplusplus
}
#endif
