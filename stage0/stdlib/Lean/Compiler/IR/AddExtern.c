// Lean compiler output
// Module: Lean.Compiler.IR.AddExtern
// Imports: import Init.While import Lean.Compiler.IR.ToIR import Lean.Compiler.LCNF.ToImpureType import Lean.Compiler.LCNF.ToImpure import Lean.Compiler.LCNF.ExplicitBoxing import Lean.Compiler.LCNF.Internalize public import Lean.Compiler.ExternAttr import Lean.Compiler.LCNF.ExplicitRC import Lean.Compiler.Options
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
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Compiler_LCNF_toImpureType(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_lowerResultType(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_internalize(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_addBoxedVersions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_runExplicitRc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Compiler_LCNF_recordFinalImpureDecl(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_run___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getOtherDeclMonoType(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedBorrowed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_IR_tracePrefixOptionName;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_addDecls(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_setDeclPublic(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__2(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__1;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0(uint8_t, lean_object*, lean_object*, uint8_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3;
static const lean_ctor_object l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___boxed__const__1 = (const lean_object*)&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "result"};
static const lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__0 = (const lean_object*)&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(180, 131, 177, 30, 113, 24, 63, 83)}};
static const lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__1 = (const lean_object*)&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__1_value;
static lean_once_cell_t l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_add_extern(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_addExtern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_defValue_4_; lean_object* v_map_5_; lean_object* v___x_6_; 
v_name_3_ = lean_ctor_get(v_opt_2_, 0);
v_defValue_4_ = lean_ctor_get(v_opt_2_, 1);
v_map_5_ = lean_ctor_get(v_opts_1_, 0);
v___x_6_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_5_, v_name_3_);
if (lean_obj_tag(v___x_6_) == 0)
{
uint8_t v___x_7_; 
v___x_7_ = lean_unbox(v_defValue_4_);
return v___x_7_;
}
else
{
lean_object* v_val_8_; 
v_val_8_ = lean_ctor_get(v___x_6_, 0);
lean_inc(v_val_8_);
lean_dec_ref(v___x_6_);
if (lean_obj_tag(v_val_8_) == 1)
{
uint8_t v_v_9_; 
v_v_9_ = lean_ctor_get_uint8(v_val_8_, 0);
lean_dec_ref(v_val_8_);
return v_v_9_;
}
else
{
uint8_t v___x_10_; 
lean_dec(v_val_8_);
v___x_10_ = lean_unbox(v_defValue_4_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0___boxed(lean_object* v_opts_11_, lean_object* v_opt_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Lean_Option_get___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0(v_opts_11_, v_opt_12_);
lean_dec_ref(v_opt_12_);
lean_dec_ref(v_opts_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___redArg(lean_object* v___y_15_){
_start:
{
lean_object* v___x_17_; lean_object* v_ngen_18_; lean_object* v_namePrefix_19_; lean_object* v_idx_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_49_; 
v___x_17_ = lean_st_ref_get(v___y_15_);
v_ngen_18_ = lean_ctor_get(v___x_17_, 2);
lean_inc_ref(v_ngen_18_);
lean_dec(v___x_17_);
v_namePrefix_19_ = lean_ctor_get(v_ngen_18_, 0);
v_idx_20_ = lean_ctor_get(v_ngen_18_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v_ngen_18_);
if (v_isSharedCheck_49_ == 0)
{
v___x_22_ = v_ngen_18_;
v_isShared_23_ = v_isSharedCheck_49_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_idx_20_);
lean_inc(v_namePrefix_19_);
lean_dec(v_ngen_18_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_49_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v_env_25_; lean_object* v_nextMacroScope_26_; lean_object* v_auxDeclNGen_27_; lean_object* v_traceState_28_; lean_object* v_cache_29_; lean_object* v_messages_30_; lean_object* v_infoState_31_; lean_object* v_snapshotTasks_32_; lean_object* v___x_34_; uint8_t v_isShared_35_; uint8_t v_isSharedCheck_47_; 
v___x_24_ = lean_st_ref_take(v___y_15_);
v_env_25_ = lean_ctor_get(v___x_24_, 0);
v_nextMacroScope_26_ = lean_ctor_get(v___x_24_, 1);
v_auxDeclNGen_27_ = lean_ctor_get(v___x_24_, 3);
v_traceState_28_ = lean_ctor_get(v___x_24_, 4);
v_cache_29_ = lean_ctor_get(v___x_24_, 5);
v_messages_30_ = lean_ctor_get(v___x_24_, 6);
v_infoState_31_ = lean_ctor_get(v___x_24_, 7);
v_snapshotTasks_32_ = lean_ctor_get(v___x_24_, 8);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_24_);
if (v_isSharedCheck_47_ == 0)
{
lean_object* v_unused_48_; 
v_unused_48_ = lean_ctor_get(v___x_24_, 2);
lean_dec(v_unused_48_);
v___x_34_ = v___x_24_;
v_isShared_35_ = v_isSharedCheck_47_;
goto v_resetjp_33_;
}
else
{
lean_inc(v_snapshotTasks_32_);
lean_inc(v_infoState_31_);
lean_inc(v_messages_30_);
lean_inc(v_cache_29_);
lean_inc(v_traceState_28_);
lean_inc(v_auxDeclNGen_27_);
lean_inc(v_nextMacroScope_26_);
lean_inc(v_env_25_);
lean_dec(v___x_24_);
v___x_34_ = lean_box(0);
v_isShared_35_ = v_isSharedCheck_47_;
goto v_resetjp_33_;
}
v_resetjp_33_:
{
lean_object* v_r_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
lean_inc(v_idx_20_);
lean_inc(v_namePrefix_19_);
v_r_36_ = l_Lean_Name_num___override(v_namePrefix_19_, v_idx_20_);
v___x_37_ = lean_unsigned_to_nat(1u);
v___x_38_ = lean_nat_add(v_idx_20_, v___x_37_);
lean_dec(v_idx_20_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 1, v___x_38_);
v___x_40_ = v___x_22_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v_namePrefix_19_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v___x_38_);
v___x_40_ = v_reuseFailAlloc_46_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_42_; 
if (v_isShared_35_ == 0)
{
lean_ctor_set(v___x_34_, 2, v___x_40_);
v___x_42_ = v___x_34_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_env_25_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_nextMacroScope_26_);
lean_ctor_set(v_reuseFailAlloc_45_, 2, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_45_, 3, v_auxDeclNGen_27_);
lean_ctor_set(v_reuseFailAlloc_45_, 4, v_traceState_28_);
lean_ctor_set(v_reuseFailAlloc_45_, 5, v_cache_29_);
lean_ctor_set(v_reuseFailAlloc_45_, 6, v_messages_30_);
lean_ctor_set(v_reuseFailAlloc_45_, 7, v_infoState_31_);
lean_ctor_set(v_reuseFailAlloc_45_, 8, v_snapshotTasks_32_);
v___x_42_ = v_reuseFailAlloc_45_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_st_ref_set(v___y_15_, v___x_42_);
v___x_44_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_44_, 0, v_r_36_);
return v___x_44_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___redArg___boxed(lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___redArg(v___y_50_);
lean_dec(v___y_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1(lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___x_56_; lean_object* v_a_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_64_; 
v___x_56_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___redArg(v___y_54_);
v_a_57_ = lean_ctor_get(v___x_56_, 0);
v_isSharedCheck_64_ = !lean_is_exclusive(v___x_56_);
if (v_isSharedCheck_64_ == 0)
{
v___x_59_ = v___x_56_;
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_a_57_);
lean_dec(v___x_56_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_64_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_62_; 
if (v_isShared_60_ == 0)
{
v___x_62_ = v___x_59_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_a_57_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1___boxed(lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1(v___y_65_, v___y_66_);
lean_dec(v___y_66_);
lean_dec_ref(v___y_65_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__2(uint8_t v___x_69_, lean_object* v_b_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v_fst_74_; 
v_fst_74_ = lean_ctor_get(v_b_70_, 0);
lean_inc(v_fst_74_);
if (lean_obj_tag(v_fst_74_) == 7)
{
lean_object* v_snd_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_102_; 
v_snd_75_ = lean_ctor_get(v_b_70_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v_b_70_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v_b_70_, 0);
lean_dec(v_unused_103_);
v___x_77_ = v_b_70_;
v_isShared_78_ = v_isSharedCheck_102_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_snd_75_);
lean_dec(v_b_70_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_102_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v_binderName_79_; lean_object* v_binderType_80_; lean_object* v_body_81_; uint8_t v___y_83_; 
v_binderName_79_ = lean_ctor_get(v_fst_74_, 0);
lean_inc(v_binderName_79_);
v_binderType_80_ = lean_ctor_get(v_fst_74_, 1);
lean_inc_ref(v_binderType_80_);
v_body_81_ = lean_ctor_get(v_fst_74_, 2);
lean_inc_ref(v_body_81_);
lean_dec_ref(v_fst_74_);
if (v___x_69_ == 0)
{
uint8_t v___x_100_; 
v___x_100_ = l_Lean_isMarkedBorrowed(v_binderType_80_);
v___y_83_ = v___x_100_;
goto v___jp_82_;
}
else
{
uint8_t v___x_101_; 
v___x_101_ = 0;
v___y_83_ = v___x_101_;
goto v___jp_82_;
}
v___jp_82_:
{
lean_object* v___x_84_; 
v___x_84_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1(v___y_71_, v___y_72_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_object* v_a_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
v_a_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_a_85_);
lean_dec_ref(v___x_84_);
v___x_86_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_86_, 0, v_a_85_);
lean_ctor_set(v___x_86_, 1, v_binderName_79_);
lean_ctor_set(v___x_86_, 2, v_binderType_80_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*3, v___y_83_);
v___x_87_ = lean_array_push(v_snd_75_, v___x_86_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 1, v___x_87_);
lean_ctor_set(v___x_77_, 0, v_body_81_);
v___x_89_ = v___x_77_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_body_81_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v___x_87_);
v___x_89_ = v_reuseFailAlloc_91_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
v_b_70_ = v___x_89_;
goto _start;
}
}
else
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_99_; 
lean_dec_ref(v_body_81_);
lean_dec_ref(v_binderType_80_);
lean_dec(v_binderName_79_);
lean_del_object(v___x_77_);
lean_dec(v_snd_75_);
v_a_92_ = lean_ctor_get(v___x_84_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_84_);
if (v_isSharedCheck_99_ == 0)
{
v___x_94_ = v___x_84_;
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_84_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_99_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_92_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
}
else
{
lean_object* v_snd_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_112_; 
v_snd_104_ = lean_ctor_get(v_b_70_, 1);
v_isSharedCheck_112_ = !lean_is_exclusive(v_b_70_);
if (v_isSharedCheck_112_ == 0)
{
lean_object* v_unused_113_; 
v_unused_113_ = lean_ctor_get(v_b_70_, 0);
lean_dec(v_unused_113_);
v___x_106_ = v_b_70_;
v_isShared_107_ = v_isSharedCheck_112_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_snd_104_);
lean_dec(v_b_70_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_112_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_fst_74_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_snd_104_);
v___x_109_ = v_reuseFailAlloc_111_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; 
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__2___boxed(lean_object* v___x_114_, lean_object* v_b_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_){
_start:
{
uint8_t v___x_1645__boxed_119_; lean_object* v_res_120_; 
v___x_1645__boxed_119_ = lean_unbox(v___x_114_);
v_res_120_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__2(v___x_1645__boxed_119_, v_b_115_, v___y_116_, v___y_117_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono(lean_object* v_externAttrData_126_, lean_object* v_declName_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_131_; 
lean_inc(v_declName_127_);
v___x_131_ = l_Lean_Compiler_LCNF_getOtherDeclMonoType(v_declName_127_, v_a_128_, v_a_129_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v_options_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_a_132_);
lean_dec_ref(v___x_131_);
v_options_133_ = lean_ctor_get(v_a_128_, 2);
v___x_134_ = ((lean_object*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__0));
v___x_135_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
v___x_136_ = l_Lean_Option_get___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__0(v_options_133_, v___x_135_);
lean_inc(v_a_132_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v_a_132_);
lean_ctor_set(v___x_137_, 1, v___x_134_);
v___x_138_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__2(v___x_136_, v___x_137_, v_a_128_, v_a_129_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v_snd_140_; lean_object* v___x_141_; uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref(v___x_138_);
v_snd_140_ = lean_ctor_get(v_a_139_, 1);
lean_inc(v_snd_140_);
lean_dec(v_a_139_);
v___x_141_ = lean_box(0);
v___x_142_ = 1;
v___x_143_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_143_, 0, v_declName_127_);
lean_ctor_set(v___x_143_, 1, v___x_141_);
lean_ctor_set(v___x_143_, 2, v_a_132_);
lean_ctor_set(v___x_143_, 3, v_snd_140_);
lean_ctor_set_uint8(v___x_143_, sizeof(void*)*4, v___x_142_);
v___x_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_144_, 0, v_externAttrData_126_);
v___x_145_ = 0;
v___x_146_ = ((lean_object*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1));
v___x_147_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_147_, 0, v___x_143_);
lean_ctor_set(v___x_147_, 1, v___x_144_);
lean_ctor_set(v___x_147_, 2, v___x_146_);
lean_ctor_set_uint8(v___x_147_, sizeof(void*)*3, v___x_145_);
lean_inc_ref(v___x_147_);
v___x_148_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_147_, v_a_129_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_155_ == 0)
{
lean_object* v_unused_156_; 
v_unused_156_ = lean_ctor_get(v___x_148_, 0);
lean_dec(v_unused_156_);
v___x_150_ = v___x_148_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_dec(v___x_148_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 0, v___x_147_);
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_147_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_164_; 
lean_dec_ref(v___x_147_);
v_a_157_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_164_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_164_ == 0)
{
v___x_159_ = v___x_148_;
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_148_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_164_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_162_; 
if (v_isShared_160_ == 0)
{
v___x_162_ = v___x_159_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_a_157_);
v___x_162_ = v_reuseFailAlloc_163_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
return v___x_162_;
}
}
}
}
else
{
lean_object* v_a_165_; lean_object* v___x_167_; uint8_t v_isShared_168_; uint8_t v_isSharedCheck_172_; 
lean_dec(v_a_132_);
lean_dec(v_declName_127_);
lean_dec(v_externAttrData_126_);
v_a_165_ = lean_ctor_get(v___x_138_, 0);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_138_);
if (v_isSharedCheck_172_ == 0)
{
v___x_167_ = v___x_138_;
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
else
{
lean_inc(v_a_165_);
lean_dec(v___x_138_);
v___x_167_ = lean_box(0);
v_isShared_168_ = v_isSharedCheck_172_;
goto v_resetjp_166_;
}
v_resetjp_166_:
{
lean_object* v___x_170_; 
if (v_isShared_168_ == 0)
{
v___x_170_ = v___x_167_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_a_165_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec(v_declName_127_);
lean_dec(v_externAttrData_126_);
v_a_173_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_131_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_131_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___boxed(lean_object* v_externAttrData_181_, lean_object* v_declName_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono(v_externAttrData_181_, v_declName_182_, v_a_183_, v_a_184_);
lean_dec(v_a_184_);
lean_dec_ref(v_a_183_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1(lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___redArg(v___y_188_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1___boxed(lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono_spec__1_spec__1(v___y_191_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v___y_191_);
return v_res_194_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_195_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__0);
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__1);
v___x_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg(lean_object* v_as_200_, size_t v_sz_201_, size_t v_i_202_, lean_object* v_b_203_, lean_object* v___y_204_){
_start:
{
uint8_t v___x_206_; 
v___x_206_ = lean_usize_dec_lt(v_i_202_, v_sz_201_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; 
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v_b_203_);
return v___x_207_;
}
else
{
lean_object* v_a_208_; lean_object* v___x_209_; 
v_a_208_ = lean_array_uget_borrowed(v_as_200_, v_i_202_);
lean_inc(v_a_208_);
v___x_209_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_208_, v___y_204_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v___x_210_; lean_object* v_toSignature_211_; lean_object* v_env_212_; lean_object* v_nextMacroScope_213_; lean_object* v_ngen_214_; lean_object* v_auxDeclNGen_215_; lean_object* v_traceState_216_; lean_object* v_messages_217_; lean_object* v_infoState_218_; lean_object* v_snapshotTasks_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_234_; 
lean_dec_ref(v___x_209_);
v___x_210_ = lean_st_ref_take(v___y_204_);
v_toSignature_211_ = lean_ctor_get(v_a_208_, 0);
v_env_212_ = lean_ctor_get(v___x_210_, 0);
v_nextMacroScope_213_ = lean_ctor_get(v___x_210_, 1);
v_ngen_214_ = lean_ctor_get(v___x_210_, 2);
v_auxDeclNGen_215_ = lean_ctor_get(v___x_210_, 3);
v_traceState_216_ = lean_ctor_get(v___x_210_, 4);
v_messages_217_ = lean_ctor_get(v___x_210_, 6);
v_infoState_218_ = lean_ctor_get(v___x_210_, 7);
v_snapshotTasks_219_ = lean_ctor_get(v___x_210_, 8);
v_isSharedCheck_234_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_234_ == 0)
{
lean_object* v_unused_235_; 
v_unused_235_ = lean_ctor_get(v___x_210_, 5);
lean_dec(v_unused_235_);
v___x_221_ = v___x_210_;
v_isShared_222_ = v_isSharedCheck_234_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_snapshotTasks_219_);
lean_inc(v_infoState_218_);
lean_inc(v_messages_217_);
lean_inc(v_traceState_216_);
lean_inc(v_auxDeclNGen_215_);
lean_inc(v_ngen_214_);
lean_inc(v_nextMacroScope_213_);
lean_inc(v_env_212_);
lean_dec(v___x_210_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_234_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v_name_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_227_; 
v_name_223_ = lean_ctor_get(v_toSignature_211_, 0);
lean_inc(v_name_223_);
v___x_224_ = l_Lean_Compiler_LCNF_recordFinalImpureDecl(v_env_212_, v_name_223_);
v___x_225_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 5, v___x_225_);
lean_ctor_set(v___x_221_, 0, v___x_224_);
v___x_227_ = v___x_221_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_nextMacroScope_213_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v_ngen_214_);
lean_ctor_set(v_reuseFailAlloc_233_, 3, v_auxDeclNGen_215_);
lean_ctor_set(v_reuseFailAlloc_233_, 4, v_traceState_216_);
lean_ctor_set(v_reuseFailAlloc_233_, 5, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_233_, 6, v_messages_217_);
lean_ctor_set(v_reuseFailAlloc_233_, 7, v_infoState_218_);
lean_ctor_set(v_reuseFailAlloc_233_, 8, v_snapshotTasks_219_);
v___x_227_ = v_reuseFailAlloc_233_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
lean_object* v___x_228_; lean_object* v___x_229_; size_t v___x_230_; size_t v___x_231_; 
v___x_228_ = lean_st_ref_set(v___y_204_, v___x_227_);
v___x_229_ = lean_box(0);
v___x_230_ = ((size_t)1ULL);
v___x_231_ = lean_usize_add(v_i_202_, v___x_230_);
v_i_202_ = v___x_231_;
v_b_203_ = v___x_229_;
goto _start;
}
}
}
else
{
return v___x_209_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___boxed(lean_object* v_as_236_, lean_object* v_sz_237_, lean_object* v_i_238_, lean_object* v_b_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
size_t v_sz_boxed_242_; size_t v_i_boxed_243_; lean_object* v_res_244_; 
v_sz_boxed_242_ = lean_unbox_usize(v_sz_237_);
lean_dec(v_sz_237_);
v_i_boxed_243_ = lean_unbox_usize(v_i_238_);
lean_dec(v_i_238_);
v_res_244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg(v_as_236_, v_sz_boxed_242_, v_i_boxed_243_, v_b_239_, v___y_240_);
lean_dec(v___y_240_);
lean_dec_ref(v_as_236_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0(uint8_t v___x_245_, lean_object* v___x_246_, lean_object* v___x_247_, uint8_t v___x_248_, size_t v___x_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Compiler_LCNF_Decl_internalize(v___x_245_, v___x_246_, v___x_247_, v___x_248_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_257_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_a_256_);
lean_dec_ref(v___x_255_);
lean_inc(v_a_256_);
v___x_257_ = l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_256_, v___y_253_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec_ref(v___x_257_);
v___x_258_ = lean_unsigned_to_nat(1u);
v___x_259_ = lean_mk_empty_array_with_capacity(v___x_258_);
v___x_260_ = lean_array_push(v___x_259_, v_a_256_);
v___x_261_ = l_Lean_Compiler_LCNF_addBoxedVersions(v___x_260_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v___x_263_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref(v___x_261_);
v___x_263_ = l_Lean_Compiler_LCNF_runExplicitRc(v_a_262_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v___x_265_; size_t v_sz_266_; lean_object* v___x_267_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref(v___x_263_);
v___x_265_ = lean_box(0);
v_sz_266_ = lean_array_size(v_a_264_);
v___x_267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg(v_a_264_, v_sz_266_, v___x_249_, v___x_265_, v___y_253_);
if (lean_obj_tag(v___x_267_) == 0)
{
lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; 
v_unused_275_ = lean_ctor_get(v___x_267_, 0);
lean_dec(v_unused_275_);
v___x_269_ = v___x_267_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_dec(v___x_267_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v_a_264_);
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_264_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
else
{
lean_object* v_a_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_283_; 
lean_dec(v_a_264_);
v_a_276_ = lean_ctor_get(v___x_267_, 0);
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_267_);
if (v_isSharedCheck_283_ == 0)
{
v___x_278_ = v___x_267_;
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_a_276_);
lean_dec(v___x_267_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_283_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___x_281_; 
if (v_isShared_279_ == 0)
{
v___x_281_ = v___x_278_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_a_276_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
}
else
{
return v___x_263_;
}
}
else
{
return v___x_261_;
}
}
else
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_291_; 
lean_dec(v_a_256_);
v_a_284_ = lean_ctor_get(v___x_257_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_257_);
if (v_isSharedCheck_291_ == 0)
{
v___x_286_ = v___x_257_;
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_257_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_291_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_289_; 
if (v_isShared_287_ == 0)
{
v___x_289_ = v___x_286_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_284_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
else
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
v_a_292_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_255_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_255_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___boxed(lean_object* v___x_300_, lean_object* v___x_301_, lean_object* v___x_302_, lean_object* v___x_303_, lean_object* v___x_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
uint8_t v___x_2771__boxed_310_; uint8_t v___x_2774__boxed_311_; size_t v___x_2775__boxed_312_; lean_object* v_res_313_; 
v___x_2771__boxed_310_ = lean_unbox(v___x_300_);
v___x_2774__boxed_311_ = lean_unbox(v___x_303_);
v___x_2775__boxed_312_ = lean_unbox_usize(v___x_304_);
lean_dec(v___x_304_);
v_res_313_ = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0(v___x_2771__boxed_310_, v___x_301_, v___x_302_, v___x_2774__boxed_311_, v___x_2775__boxed_312_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0(size_t v_sz_314_, size_t v_i_315_, lean_object* v_bs_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
uint8_t v___x_320_; 
v___x_320_ = lean_usize_dec_lt(v_i_315_, v_sz_314_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; 
v___x_321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_321_, 0, v_bs_316_);
return v___x_321_;
}
else
{
lean_object* v_v_322_; lean_object* v_fvarId_323_; lean_object* v_binderName_324_; lean_object* v_type_325_; uint8_t v_borrow_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_349_; 
v_v_322_ = lean_array_uget(v_bs_316_, v_i_315_);
v_fvarId_323_ = lean_ctor_get(v_v_322_, 0);
v_binderName_324_ = lean_ctor_get(v_v_322_, 1);
v_type_325_ = lean_ctor_get(v_v_322_, 2);
v_borrow_326_ = lean_ctor_get_uint8(v_v_322_, sizeof(void*)*3);
v_isSharedCheck_349_ = !lean_is_exclusive(v_v_322_);
if (v_isSharedCheck_349_ == 0)
{
v___x_328_ = v_v_322_;
v_isShared_329_ = v_isSharedCheck_349_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_type_325_);
lean_inc(v_binderName_324_);
lean_inc(v_fvarId_323_);
lean_dec(v_v_322_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_349_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_330_; 
v___x_330_ = l_Lean_Compiler_LCNF_toImpureType(v_type_325_, v___y_317_, v___y_318_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_332_; lean_object* v_bs_x27_333_; lean_object* v___x_335_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref(v___x_330_);
v___x_332_ = lean_unsigned_to_nat(0u);
v_bs_x27_333_ = lean_array_uset(v_bs_316_, v_i_315_, v___x_332_);
if (v_isShared_329_ == 0)
{
lean_ctor_set(v___x_328_, 2, v_a_331_);
v___x_335_ = v___x_328_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_fvarId_323_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_binderName_324_);
lean_ctor_set(v_reuseFailAlloc_340_, 2, v_a_331_);
lean_ctor_set_uint8(v_reuseFailAlloc_340_, sizeof(void*)*3, v_borrow_326_);
v___x_335_ = v_reuseFailAlloc_340_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
size_t v___x_336_; size_t v___x_337_; lean_object* v___x_338_; 
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_add(v_i_315_, v___x_336_);
v___x_338_ = lean_array_uset(v_bs_x27_333_, v_i_315_, v___x_335_);
v_i_315_ = v___x_337_;
v_bs_316_ = v___x_338_;
goto _start;
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_del_object(v___x_328_);
lean_dec(v_binderName_324_);
lean_dec(v_fvarId_323_);
lean_dec_ref(v_bs_316_);
v_a_341_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_330_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_330_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0___boxed(lean_object* v_sz_350_, lean_object* v_i_351_, lean_object* v_bs_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
size_t v_sz_boxed_356_; size_t v_i_boxed_357_; lean_object* v_res_358_; 
v_sz_boxed_356_ = lean_unbox_usize(v_sz_350_);
lean_dec(v_sz_350_);
v_i_boxed_357_ = lean_unbox_usize(v_i_351_);
lean_dec(v_i_351_);
v_res_358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0(v_sz_boxed_356_, v_i_boxed_357_, v_bs_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_358_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_box(0);
v___x_360_ = lean_unsigned_to_nat(16u);
v___x_361_ = lean_mk_array(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__0);
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v___x_362_);
return v___x_364_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2(void){
_start:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1);
v___x_366_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
lean_ctor_set(v___x_366_, 2, v___x_365_);
lean_ctor_set(v___x_366_, 3, v___x_365_);
lean_ctor_set(v___x_366_, 4, v___x_365_);
lean_ctor_set(v___x_366_, 5, v___x_365_);
return v___x_366_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__2);
v___x_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v___x_367_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure(lean_object* v_externAttrData_372_, lean_object* v_decl_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
lean_object* v_toSignature_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_431_; 
v_toSignature_377_ = lean_ctor_get(v_decl_373_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v_decl_373_);
if (v_isSharedCheck_431_ == 0)
{
lean_object* v_unused_432_; lean_object* v_unused_433_; 
v_unused_432_ = lean_ctor_get(v_decl_373_, 2);
lean_dec(v_unused_432_);
v_unused_433_ = lean_ctor_get(v_decl_373_, 1);
lean_dec(v_unused_433_);
v___x_379_ = v_decl_373_;
v_isShared_380_ = v_isSharedCheck_431_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_toSignature_377_);
lean_dec(v_decl_373_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_431_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_name_381_; lean_object* v_levelParams_382_; lean_object* v_type_383_; lean_object* v_params_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_430_; 
v_name_381_ = lean_ctor_get(v_toSignature_377_, 0);
v_levelParams_382_ = lean_ctor_get(v_toSignature_377_, 1);
v_type_383_ = lean_ctor_get(v_toSignature_377_, 2);
v_params_384_ = lean_ctor_get(v_toSignature_377_, 3);
v_isSharedCheck_430_ = !lean_is_exclusive(v_toSignature_377_);
if (v_isSharedCheck_430_ == 0)
{
v___x_386_ = v_toSignature_377_;
v_isShared_387_ = v_isSharedCheck_430_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_params_384_);
lean_inc(v_type_383_);
lean_inc(v_levelParams_382_);
lean_inc(v_name_381_);
lean_dec(v_toSignature_377_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_430_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_array_get_size(v_params_384_);
v___x_389_ = l_Lean_Compiler_LCNF_lowerResultType(v_type_383_, v___x_388_, v_a_374_, v_a_375_);
lean_dec_ref(v_type_383_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; size_t v_sz_391_; size_t v___x_392_; lean_object* v___x_393_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_a_390_);
lean_dec_ref(v___x_389_);
v_sz_391_ = lean_array_size(v_params_384_);
v___x_392_ = ((size_t)0ULL);
v___x_393_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__0(v_sz_391_, v___x_392_, v_params_384_, v_a_374_, v_a_375_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; uint8_t v___x_395_; uint8_t v___x_396_; lean_object* v___x_398_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_a_394_);
lean_dec_ref(v___x_393_);
v___x_395_ = 1;
v___x_396_ = 1;
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 3, v_a_394_);
lean_ctor_set(v___x_386_, 2, v_a_390_);
v___x_398_ = v___x_386_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_name_381_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_levelParams_382_);
lean_ctor_set(v_reuseFailAlloc_413_, 2, v_a_390_);
lean_ctor_set(v_reuseFailAlloc_413_, 3, v_a_394_);
v___x_398_ = v_reuseFailAlloc_413_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; uint8_t v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*4, v___x_396_);
v___x_399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_399_, 0, v_externAttrData_372_);
v___x_400_ = 0;
v___x_401_ = ((lean_object*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono___closed__1));
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 2, v___x_401_);
lean_ctor_set(v___x_379_, 1, v___x_399_);
lean_ctor_set(v___x_379_, 0, v___x_398_);
v___x_403_ = v___x_379_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v___x_401_);
v___x_403_ = v_reuseFailAlloc_412_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___f_408_; lean_object* v___x_409_; uint8_t v___x_410_; lean_object* v___x_411_; 
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*3, v___x_400_);
v___x_404_ = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__1);
v___x_405_ = lean_box(v___x_395_);
v___x_406_ = lean_box(v___x_400_);
v___x_407_ = ((lean_object*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___boxed__const__1));
v___f_408_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___lam__0___boxed), 10, 5);
lean_closure_set(v___f_408_, 0, v___x_405_);
lean_closure_set(v___f_408_, 1, v___x_403_);
lean_closure_set(v___f_408_, 2, v___x_404_);
lean_closure_set(v___f_408_, 3, v___x_406_);
lean_closure_set(v___f_408_, 4, v___x_407_);
v___x_409_ = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___closed__3);
v___x_410_ = 2;
v___x_411_ = l_Lean_Compiler_LCNF_CompilerM_run___redArg(v___f_408_, v___x_409_, v___x_410_, v_a_374_, v_a_375_);
return v___x_411_;
}
}
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
lean_dec(v_a_390_);
lean_del_object(v___x_386_);
lean_dec(v_levelParams_382_);
lean_dec(v_name_381_);
lean_del_object(v___x_379_);
lean_dec(v_externAttrData_372_);
v_a_414_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_393_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_393_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_object* v_a_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_429_; 
lean_del_object(v___x_386_);
lean_dec_ref(v_params_384_);
lean_dec(v_levelParams_382_);
lean_dec(v_name_381_);
lean_del_object(v___x_379_);
lean_dec(v_externAttrData_372_);
v_a_422_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_429_ == 0)
{
v___x_424_ = v___x_389_;
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_a_422_);
lean_dec(v___x_389_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_429_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_427_; 
if (v_isShared_425_ == 0)
{
v___x_427_ = v___x_424_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure___boxed(lean_object* v_externAttrData_434_, lean_object* v_decl_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure(v_externAttrData_434_, v_decl_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1(lean_object* v_as_440_, size_t v_sz_441_, size_t v_i_442_, lean_object* v_b_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg(v_as_440_, v_sz_441_, v_i_442_, v_b_443_, v___y_447_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___boxed(lean_object* v_as_450_, lean_object* v_sz_451_, lean_object* v_i_452_, lean_object* v_b_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
size_t v_sz_boxed_459_; size_t v_i_boxed_460_; lean_object* v_res_461_; 
v_sz_boxed_459_ = lean_unbox_usize(v_sz_451_);
lean_dec(v_sz_451_);
v_i_boxed_460_ = lean_unbox_usize(v_i_452_);
lean_dec(v_i_452_);
v_res_461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1(v_as_450_, v_sz_boxed_459_, v_i_boxed_460_, v_b_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
lean_dec_ref(v_as_450_);
return v_res_461_;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_465_ = ((lean_object*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__1));
v___x_466_ = l_Lean_IR_tracePrefixOptionName;
v___x_467_ = l_Lean_Name_append(v___x_466_, v___x_465_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr(lean_object* v_decls_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = l_Lean_IR_toIR(v_decls_468_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_472_) == 0)
{
lean_object* v_a_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v_a_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_a_473_);
lean_dec_ref(v___x_472_);
v___x_474_ = ((lean_object*)(l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__1));
v___x_475_ = lean_obj_once(&l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2, &l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2_once, _init_l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___closed__2);
lean_inc(v_a_473_);
v___x_476_ = l___private_Lean_Compiler_IR_CompilerM_0__Lean_IR_logDeclsAux(v___x_475_, v___x_474_, v_a_473_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v___x_477_; 
lean_dec_ref(v___x_476_);
v___x_477_ = l_Lean_IR_addDecls(v_a_473_, v_a_469_, v_a_470_);
lean_dec(v_a_473_);
return v___x_477_;
}
else
{
lean_dec(v_a_473_);
return v___x_476_;
}
}
else
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
v_a_478_ = lean_ctor_get(v___x_472_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_472_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_472_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr___boxed(lean_object* v_decls_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr(v_decls_486_, v_a_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_a_487_);
lean_dec_ref(v_decls_486_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* lean_add_extern(lean_object* v_declName_491_, lean_object* v_externAttrData_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___y_497_; lean_object* v___y_498_; uint8_t v___x_520_; 
v___x_520_ = l_Lean_isPrivateName(v_declName_491_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v_env_522_; lean_object* v_nextMacroScope_523_; lean_object* v_ngen_524_; lean_object* v_auxDeclNGen_525_; lean_object* v_traceState_526_; lean_object* v_messages_527_; lean_object* v_infoState_528_; lean_object* v_snapshotTasks_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_539_; 
v___x_521_ = lean_st_ref_take(v_a_494_);
v_env_522_ = lean_ctor_get(v___x_521_, 0);
v_nextMacroScope_523_ = lean_ctor_get(v___x_521_, 1);
v_ngen_524_ = lean_ctor_get(v___x_521_, 2);
v_auxDeclNGen_525_ = lean_ctor_get(v___x_521_, 3);
v_traceState_526_ = lean_ctor_get(v___x_521_, 4);
v_messages_527_ = lean_ctor_get(v___x_521_, 6);
v_infoState_528_ = lean_ctor_get(v___x_521_, 7);
v_snapshotTasks_529_ = lean_ctor_get(v___x_521_, 8);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v___x_521_, 5);
lean_dec(v_unused_540_);
v___x_531_ = v___x_521_;
v_isShared_532_ = v_isSharedCheck_539_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_snapshotTasks_529_);
lean_inc(v_infoState_528_);
lean_inc(v_messages_527_);
lean_inc(v_traceState_526_);
lean_inc(v_auxDeclNGen_525_);
lean_inc(v_ngen_524_);
lean_inc(v_nextMacroScope_523_);
lean_inc(v_env_522_);
lean_dec(v___x_521_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_539_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
lean_inc(v_declName_491_);
v___x_533_ = l_Lean_Compiler_LCNF_setDeclPublic(v_env_522_, v_declName_491_);
v___x_534_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure_spec__1___redArg___closed__2);
if (v_isShared_532_ == 0)
{
lean_ctor_set(v___x_531_, 5, v___x_534_);
lean_ctor_set(v___x_531_, 0, v___x_533_);
v___x_536_ = v___x_531_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_533_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_nextMacroScope_523_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_ngen_524_);
lean_ctor_set(v_reuseFailAlloc_538_, 3, v_auxDeclNGen_525_);
lean_ctor_set(v_reuseFailAlloc_538_, 4, v_traceState_526_);
lean_ctor_set(v_reuseFailAlloc_538_, 5, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_538_, 6, v_messages_527_);
lean_ctor_set(v_reuseFailAlloc_538_, 7, v_infoState_528_);
lean_ctor_set(v_reuseFailAlloc_538_, 8, v_snapshotTasks_529_);
v___x_536_ = v_reuseFailAlloc_538_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
lean_object* v___x_537_; 
v___x_537_ = lean_st_ref_set(v_a_494_, v___x_536_);
v___y_497_ = v_a_493_;
v___y_498_ = v_a_494_;
goto v___jp_496_;
}
}
}
else
{
v___y_497_ = v_a_493_;
v___y_498_ = v_a_494_;
goto v___jp_496_;
}
v___jp_496_:
{
lean_object* v___x_499_; 
lean_inc(v_externAttrData_492_);
v___x_499_ = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addMono(v_externAttrData_492_, v_declName_491_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_501_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref(v___x_499_);
v___x_501_ = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addImpure(v_externAttrData_492_, v_a_500_, v___y_497_, v___y_498_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_503_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref(v___x_501_);
v___x_503_ = l___private_Lean_Compiler_IR_AddExtern_0__Lean_IR_addExtern_addIr(v_a_502_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v_a_502_);
return v___x_503_;
}
else
{
lean_object* v_a_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
v_a_504_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_511_ == 0)
{
v___x_506_ = v___x_501_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_a_504_);
lean_dec(v___x_501_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
}
else
{
lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_519_; 
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v_externAttrData_492_);
v_a_512_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_519_ == 0)
{
v___x_514_ = v___x_499_;
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_499_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_519_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_517_; 
if (v_isShared_515_ == 0)
{
v___x_517_ = v___x_514_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_a_512_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_addExtern___boxed(lean_object* v_declName_541_, lean_object* v_externAttrData_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = lean_add_extern(v_declName_541_, v_externAttrData_542_, v_a_543_, v_a_544_);
return v_res_546_;
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_IR_ToIR(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ExplicitBoxing(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ExplicitRC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_IR_AddExtern(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_ToIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToImpure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ExplicitRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_IR_AddExtern(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToImpureType(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToImpure(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ExplicitBoxing(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ExternAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ExplicitRC(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_AddExtern(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIR(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToImpureType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToImpure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExternAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ExplicitRC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_IR_AddExtern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_IR_AddExtern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_IR_AddExtern(builtin);
}
#ifdef __cplusplus
}
#endif
