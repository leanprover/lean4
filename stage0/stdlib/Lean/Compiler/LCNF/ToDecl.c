// Lean compiler output
// Module: Lean.Compiler.LCNF.ToDecl
// Imports: public import Lean.Compiler.InitAttr public import Lean.Compiler.LCNF.ToLCNF import Lean.Compiler.Options import Lean.Meta.Transform import Lean.Meta.Match.MatcherInfo import Init.While import Lean.Compiler.ExportAttr
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
extern lean_object* l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_isMarkedBorrowed(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
lean_object* l_Lean_Compiler_mkUnsafeRecName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
uint8_t l_Lean_isExport(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_Compiler_getInlineAttribute_x3f(lean_object*, lean_object*);
lean_object* l_Lean_getExternAttrData_x3f(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_has_init_attr(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Compiler_isUnsafeRecName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(uint8_t, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " Declaration "};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__1;
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 321, .m_capacity = 321, .m_length = 320, .m_data = " is marked as `export` but some of its parameters have borrow annotations.\n Consider using `set_option compiler.ignoreBorrowAnnotation true in` to suppress the borrow annotations in its type.\n If the declaration is part of an `export`/`extern` pair make sure to also suppress the annotations at the `extern` declaration."};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__2_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__3;
static const lean_ctor_object l_Lean_Compiler_LCNF_toDecl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__4 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__4_value;
static const lean_ctor_object l_Lean_Compiler_LCNF_toDecl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__5 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__5_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Compiler_LCNF_toDecl___closed__6;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__7;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__8;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__9;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__10;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__11;
static const lean_array_object l_Lean_Compiler_LCNF_toDecl___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__12 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__12_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__13;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__14;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__15;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__16;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__17;
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declaration `"};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__18 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__18_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__19;
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "` does not have a value"};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__20 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__20_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__21;
static const lean_string_object l_Lean_Compiler_LCNF_toDecl___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` not found"};
static const lean_object* l_Lean_Compiler_LCNF_toDecl___closed__22 = (const lean_object*)&l_Lean_Compiler_LCNF_toDecl___closed__22_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_toDecl___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_toDecl___closed__23;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4(uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(lean_object* v_declName_1_, lean_object* v_a_2_){
_start:
{
lean_object* v___x_4_; lean_object* v_env_5_; lean_object* v___x_6_; uint8_t v___x_7_; lean_object* v___x_8_; 
v___x_4_ = lean_st_ref_get(v_a_2_);
v_env_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc_ref_n(v_env_5_, 2);
lean_dec(v___x_4_);
lean_inc(v_declName_1_);
v___x_6_ = l_Lean_Compiler_mkUnsafeRecName(v_declName_1_);
v___x_7_ = 0;
v___x_8_ = l_Lean_Environment_find_x3f(v_env_5_, v___x_6_, v___x_7_);
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_9_ = l_Lean_Environment_find_x3f(v_env_5_, v_declName_1_, v___x_7_);
v___x_10_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; 
lean_dec_ref(v_env_5_);
lean_dec(v_declName_1_);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_8_);
return v___x_11_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_res_12_;
v_res_12_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v_declName_1_, v_a_2_);
stack->m_obj
 = v_res_12_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg___boxed(lean_object* v_declName_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v_declName_13_, v_a_14_);
lean_dec(v_a_14_);
return v_res_16_;
}
}
lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f(lean_object* v_declName_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v_declName_17_, v_a_19_);
return v___x_21_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_getDeclInfo_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_17_ = stack[0].m_obj;
lean_object* v_a_18_ = stack[1].m_obj;
lean_object* v_a_19_ = stack[2].m_obj;
lean_object* v_res_22_;
v_res_22_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f(v_declName_17_, v_a_18_, v_a_19_);
stack->m_obj
 = v_res_22_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___boxed(lean_object* v_declName_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f(v_declName_23_, v_a_24_, v_a_25_);
lean_dec(v_a_25_);
lean_dec_ref(v_a_24_);
return v_res_27_;
}
}
lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(lean_object* v_declName_28_, lean_object* v_a_29_){
_start:
{
lean_object* v___x_31_; lean_object* v_env_32_; uint8_t v___x_33_; lean_object* v___x_34_; 
v___x_31_ = lean_st_ref_get(v_a_29_);
v_env_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc_ref_n(v_env_32_, 2);
lean_dec(v___x_31_);
v___x_33_ = 0;
lean_inc(v_declName_28_);
v___x_34_ = l_Lean_Environment_find_x3f(v_env_32_, v_declName_28_, v___x_33_);
if (lean_obj_tag(v___x_34_) == 1)
{
lean_object* v_val_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_62_; 
v_val_35_ = lean_ctor_get(v___x_34_, 0);
v_isSharedCheck_62_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_62_ == 0)
{
v___x_37_ = v___x_34_;
v_isShared_38_ = v_isSharedCheck_62_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_val_35_);
lean_dec(v___x_34_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_62_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
uint8_t v___x_39_; uint8_t v___y_41_; 
v___x_39_ = l_Lean_ConstantInfo_isUnsafe(v_val_35_);
if (v___x_39_ == 0)
{
uint8_t v___x_57_; 
v___x_57_ = 1;
if (lean_obj_tag(v_val_35_) == 3)
{
lean_dec_ref_known(v_val_35_, 1);
v___y_41_ = v___x_57_;
goto v___jp_40_;
}
else
{
lean_dec(v_val_35_);
if (v___x_39_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_del_object(v___x_37_);
lean_dec_ref(v_env_32_);
lean_dec(v_declName_28_);
v___x_58_ = lean_box(v___x_57_);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
else
{
v___y_41_ = v___x_39_;
goto v___jp_40_;
}
}
}
else
{
lean_object* v___x_60_; lean_object* v___x_61_; 
lean_del_object(v___x_37_);
lean_dec(v_val_35_);
lean_dec_ref(v_env_32_);
lean_dec(v_declName_28_);
v___x_60_ = lean_box(v___x_33_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
v___jp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = l_Lean_Compiler_mkUnsafeRecName(v_declName_28_);
v___x_43_ = l_Lean_Environment_find_x3f(v_env_32_, v___x_42_, v___x_39_);
if (lean_obj_tag(v___x_43_) == 0)
{
lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_44_ = lean_box(v___y_41_);
if (v_isShared_38_ == 0)
{
lean_ctor_set_tag(v___x_37_, 0);
lean_ctor_set(v___x_37_, 0, v___x_44_);
v___x_46_ = v___x_37_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_44_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
else
{
lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_55_; 
lean_del_object(v___x_37_);
v_isSharedCheck_55_ = !lean_is_exclusive(v___x_43_);
if (v_isSharedCheck_55_ == 0)
{
lean_object* v_unused_56_; 
v_unused_56_ = lean_ctor_get(v___x_43_, 0);
lean_dec(v_unused_56_);
v___x_49_ = v___x_43_;
v_isShared_50_ = v_isSharedCheck_55_;
goto v_resetjp_48_;
}
else
{
lean_dec(v___x_43_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_55_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; lean_object* v___x_53_; 
v___x_51_ = lean_box(v___x_39_);
if (v_isShared_50_ == 0)
{
lean_ctor_set_tag(v___x_49_, 0);
lean_ctor_set(v___x_49_, 0, v___x_51_);
v___x_53_ = v___x_49_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_51_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
}
}
}
else
{
uint8_t v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
lean_dec(v___x_34_);
lean_dec_ref(v_env_32_);
lean_dec(v_declName_28_);
v___x_63_ = 1;
v___x_64_ = lean_box(v___x_63_);
v___x_65_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
return v___x_65_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_28_ = stack[0].m_obj;
lean_object* v_a_29_ = stack[1].m_obj;
lean_object* v_res_66_;
v_res_66_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v_declName_28_, v_a_29_);
stack->m_obj
 = v_res_66_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg___boxed(lean_object* v_declName_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v_declName_67_, v_a_68_);
lean_dec(v_a_68_);
return v_res_70_;
}
}
lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe(lean_object* v_declName_71_, lean_object* v_a_72_, lean_object* v_a_73_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v_declName_71_, v_a_73_);
return v___x_75_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_declIsNotUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_71_ = stack[0].m_obj;
lean_object* v_a_72_ = stack[1].m_obj;
lean_object* v_a_73_ = stack[2].m_obj;
lean_object* v_res_76_;
v_res_76_ = l_Lean_Compiler_LCNF_declIsNotUnsafe(v_declName_71_, v_a_72_, v_a_73_);
stack->m_obj
 = v_res_76_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___boxed(lean_object* v_declName_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_Compiler_LCNF_declIsNotUnsafe(v_declName_77_, v_a_78_, v_a_79_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
return v_res_81_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(lean_object* v_opts_82_, lean_object* v_opt_83_){
_start:
{
lean_object* v_name_84_; lean_object* v_defValue_85_; lean_object* v_map_86_; lean_object* v___x_87_; 
v_name_84_ = lean_ctor_get(v_opt_83_, 0);
v_defValue_85_ = lean_ctor_get(v_opt_83_, 1);
v_map_86_ = lean_ctor_get(v_opts_82_, 0);
v___x_87_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_86_, v_name_84_);
if (lean_obj_tag(v___x_87_) == 0)
{
uint8_t v___x_88_; 
v___x_88_ = lean_unbox(v_defValue_85_);
return v___x_88_;
}
else
{
lean_object* v_val_89_; 
v_val_89_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_val_89_);
lean_dec_ref_known(v___x_87_, 1);
if (lean_obj_tag(v_val_89_) == 1)
{
uint8_t v_v_90_; 
v_v_90_ = lean_ctor_get_uint8(v_val_89_, 0);
lean_dec_ref_known(v_val_89_, 0);
return v_v_90_;
}
else
{
uint8_t v___x_91_; 
lean_dec(v_val_89_);
v___x_91_ = lean_unbox(v_defValue_85_);
return v___x_91_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_82_ = stack[0].m_obj;
lean_object* v_opt_83_ = stack[1].m_obj;
uint8_t v_res_92_;
v_res_92_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v_opts_82_, v_opt_83_);
stack->m_num = v_res_92_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0___boxed(lean_object* v_opts_93_, lean_object* v_opt_94_){
_start:
{
uint8_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v_opts_93_, v_opt_94_);
lean_dec_ref(v_opt_94_);
lean_dec_ref(v_opts_93_);
v_r_96_ = lean_box(v_res_95_);
return v_r_96_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_97_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0);
v___x_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_100_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_101_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1);
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
lean_ctor_set(v___x_103_, 2, v___x_102_);
lean_ctor_set(v___x_103_, 3, v___x_102_);
lean_ctor_set(v___x_103_, 4, v___x_101_);
lean_ctor_set(v___x_103_, 5, v___x_101_);
lean_ctor_set(v___x_103_, 6, v___x_101_);
lean_ctor_set(v___x_103_, 7, v___x_101_);
lean_ctor_set(v___x_103_, 8, v___x_101_);
lean_ctor_set(v___x_103_, 9, v___x_101_);
lean_ctor_set(v___x_103_, 10, v___x_101_);
lean_ctor_set(v___x_103_, 11, v___x_100_);
return v___x_103_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(lean_object* v_msg_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_){
_start:
{
lean_object* v_ref_110_; lean_object* v___x_111_; lean_object* v_env_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_ref_110_ = lean_ctor_get(v___y_107_, 2);
v___x_111_ = lean_st_ref_get(v___y_108_);
v_env_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc_ref(v_env_112_);
lean_dec(v___x_111_);
v___x_113_ = lean_st_ref_get(v___y_106_);
v___x_114_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_105_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_137_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_137_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_137_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_137_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v_lctx_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_135_; 
v_lctx_119_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_135_ == 0)
{
lean_object* v_unused_136_; 
v_unused_136_ = lean_ctor_get(v___x_113_, 1);
lean_dec(v_unused_136_);
v___x_121_ = v___x_113_;
v_isShared_122_ = v_isSharedCheck_135_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_lctx_119_);
lean_dec(v___x_113_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_135_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
uint8_t v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_123_ = lean_unbox(v_a_115_);
lean_dec(v_a_115_);
v___x_124_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_119_, v___x_123_);
lean_dec_ref(v_lctx_119_);
v___x_125_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_107_);
v___x_126_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2);
v___x_127_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_127_, 0, v_env_112_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
lean_ctor_set(v___x_127_, 2, v___x_124_);
lean_ctor_set(v___x_127_, 3, v___x_125_);
if (v_isShared_122_ == 0)
{
lean_ctor_set_tag(v___x_121_, 3);
lean_ctor_set(v___x_121_, 1, v_msg_104_);
lean_ctor_set(v___x_121_, 0, v___x_127_);
v___x_129_ = v___x_121_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___x_127_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v_msg_104_);
v___x_129_ = v_reuseFailAlloc_134_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; lean_object* v___x_132_; 
lean_inc(v_ref_110_);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v_ref_110_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
if (v_isShared_118_ == 0)
{
lean_ctor_set_tag(v___x_117_, 1);
lean_ctor_set(v___x_117_, 0, v___x_130_);
v___x_132_ = v___x_117_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec(v___x_113_);
lean_dec_ref(v_env_112_);
lean_dec_ref(v_msg_104_);
v_a_138_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_114_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_114_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_104_ = stack[0].m_obj;
lean_object* v___y_105_ = stack[1].m_obj;
lean_object* v___y_106_ = stack[2].m_obj;
lean_object* v___y_107_ = stack[3].m_obj;
lean_object* v___y_108_ = stack[4].m_obj;
lean_object* v_res_146_;
v_res_146_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v_msg_104_, v___y_105_, v___y_106_, v___y_107_, v___y_108_);
stack->m_obj
 = v_res_146_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___boxed(lean_object* v_msg_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v_msg_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_153_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2(lean_object* v_00_u03b1_154_, lean_object* v_msg_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v_msg_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
return v___x_161_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_155_ = stack[1].m_obj;
lean_object* v___y_156_ = stack[2].m_obj;
lean_object* v___y_157_ = stack[3].m_obj;
lean_object* v___y_158_ = stack[4].m_obj;
lean_object* v___y_159_ = stack[5].m_obj;
lean_object* v_res_162_;
v_res_162_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2(lean_box(0), v_msg_155_, v___y_156_, v___y_157_, v___y_158_, v___y_159_);
stack->m_obj
 = v_res_162_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___boxed(lean_object* v_00_u03b1_163_, lean_object* v_msg_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v_res_170_; 
v_res_170_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2(v_00_u03b1_163_, v_msg_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
lean_dec(v___y_168_);
lean_dec_ref(v___y_167_);
lean_dec(v___y_166_);
lean_dec_ref(v___y_165_);
return v_res_170_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0(lean_object* v_k_171_, lean_object* v_b_172_, lean_object* v_c_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_){
_start:
{
lean_object* v___x_179_; 
lean_inc(v___y_177_);
lean_inc_ref(v___y_176_);
lean_inc(v___y_175_);
lean_inc_ref(v___y_174_);
v___x_179_ = lean_apply_7(v_k_171_, v_b_172_, v_c_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, lean_box(0));
return v___x_179_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_171_ = stack[0].m_obj;
lean_object* v_b_172_ = stack[1].m_obj;
lean_object* v_c_173_ = stack[2].m_obj;
lean_object* v___y_174_ = stack[3].m_obj;
lean_object* v___y_175_ = stack[4].m_obj;
lean_object* v___y_176_ = stack[5].m_obj;
lean_object* v___y_177_ = stack[6].m_obj;
lean_object* v_res_180_;
v_res_180_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0(v_k_171_, v_b_172_, v_c_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
stack->m_obj
 = v_res_180_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0___boxed(lean_object* v_k_181_, lean_object* v_b_182_, lean_object* v_c_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0(v_k_181_, v_b_182_, v_c_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_189_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(lean_object* v_e_190_, lean_object* v_k_191_, uint8_t v_cleanupAnnotations_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v___f_198_; uint8_t v___x_199_; uint8_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___f_198_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_198_, 0, v_k_191_);
v___x_199_ = 1;
v___x_200_ = 0;
v___x_201_ = lean_box(0);
v___x_202_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_190_, v___x_199_, v___x_200_, v___x_199_, v___x_200_, v___x_201_, v___f_198_, v_cleanupAnnotations_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_202_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_202_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
else
{
lean_object* v_a_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
v_a_211_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_202_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_a_211_);
lean_dec(v___x_202_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_190_ = stack[0].m_obj;
lean_object* v_k_191_ = stack[1].m_obj;
uint8_t v_cleanupAnnotations_192_ = stack[2].m_num;
lean_object* v___y_193_ = stack[3].m_obj;
lean_object* v___y_194_ = stack[4].m_obj;
lean_object* v___y_195_ = stack[5].m_obj;
lean_object* v___y_196_ = stack[6].m_obj;
lean_object* v_res_219_;
v_res_219_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_e_190_, v_k_191_, v_cleanupAnnotations_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___boxed(lean_object* v_e_220_, lean_object* v_k_221_, lean_object* v_cleanupAnnotations_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_228_; lean_object* v_res_229_; 
v_cleanupAnnotations_boxed_228_ = lean_unbox(v_cleanupAnnotations_222_);
v_res_229_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_e_220_, v_k_221_, v_cleanupAnnotations_boxed_228_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec(v___y_226_);
lean_dec_ref(v___y_225_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
return v_res_229_;
}
}
lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5(lean_object* v_00_u03b1_230_, lean_object* v_e_231_, lean_object* v_k_232_, uint8_t v_cleanupAnnotations_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_e_231_, v_k_232_, v_cleanupAnnotations_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
return v___x_239_;
}
}
LEAN_EXPORT void l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_231_ = stack[1].m_obj;
lean_object* v_k_232_ = stack[2].m_obj;
uint8_t v_cleanupAnnotations_233_ = stack[3].m_num;
lean_object* v___y_234_ = stack[4].m_obj;
lean_object* v___y_235_ = stack[5].m_obj;
lean_object* v___y_236_ = stack[6].m_obj;
lean_object* v___y_237_ = stack[7].m_obj;
lean_object* v_res_240_;
v_res_240_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5(lean_box(0), v_e_231_, v_k_232_, v_cleanupAnnotations_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
stack->m_obj
 = v_res_240_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___boxed(lean_object* v_00_u03b1_241_, lean_object* v_e_242_, lean_object* v_k_243_, lean_object* v_cleanupAnnotations_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_250_; lean_object* v_res_251_; 
v_cleanupAnnotations_boxed_250_ = lean_unbox(v_cleanupAnnotations_244_);
v_res_251_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5(v_00_u03b1_241_, v_e_242_, v_k_243_, v_cleanupAnnotations_boxed_250_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
return v_res_251_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(uint8_t v___x_252_, lean_object* v_a_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v_snd_259_; 
v_snd_259_ = lean_ctor_get(v_a_253_, 1);
lean_inc(v_snd_259_);
if (lean_obj_tag(v_snd_259_) == 7)
{
lean_object* v_fst_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_287_; 
v_fst_260_ = lean_ctor_get(v_a_253_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v_a_253_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v_a_253_, 1);
lean_dec(v_unused_288_);
v___x_262_ = v_a_253_;
v_isShared_263_ = v_isSharedCheck_287_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_fst_260_);
lean_dec(v_a_253_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_287_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v_binderName_264_; lean_object* v_binderType_265_; lean_object* v_body_266_; uint8_t v___y_268_; 
v_binderName_264_ = lean_ctor_get(v_snd_259_, 0);
lean_inc(v_binderName_264_);
v_binderType_265_ = lean_ctor_get(v_snd_259_, 1);
lean_inc_ref(v_binderType_265_);
v_body_266_ = lean_ctor_get(v_snd_259_, 2);
lean_inc_ref(v_body_266_);
lean_dec_ref_known(v_snd_259_, 3);
if (v___x_252_ == 0)
{
uint8_t v___x_285_; 
v___x_285_ = l_Lean_isMarkedBorrowed(v_binderType_265_);
v___y_268_ = v___x_285_;
goto v___jp_267_;
}
else
{
uint8_t v___x_286_; 
v___x_286_ = 0;
v___y_268_ = v___x_286_;
goto v___jp_267_;
}
v___jp_267_:
{
uint8_t v___x_269_; lean_object* v___x_270_; 
v___x_269_ = 0;
v___x_270_ = l_Lean_Compiler_LCNF_mkParam(v___x_269_, v_binderName_264_, v_binderType_265_, v___y_268_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref_known(v___x_270_, 1);
v___x_272_ = lean_array_push(v_fst_260_, v_a_271_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v_body_266_);
lean_ctor_set(v___x_262_, 0, v___x_272_);
v___x_274_ = v___x_262_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_body_266_);
v___x_274_ = v_reuseFailAlloc_276_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
v_a_253_ = v___x_274_;
goto _start;
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec_ref(v_body_266_);
lean_del_object(v___x_262_);
lean_dec(v_fst_260_);
v_a_277_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_270_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_270_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
}
else
{
lean_object* v_fst_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_297_; 
v_fst_289_ = lean_ctor_get(v_a_253_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v_a_253_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; 
v_unused_298_ = lean_ctor_get(v_a_253_, 1);
lean_dec(v_unused_298_);
v___x_291_ = v_a_253_;
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_fst_289_);
lean_dec(v_a_253_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_297_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_fst_289_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_snd_259_);
v___x_294_ = v_reuseFailAlloc_296_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
lean_object* v___x_295_; 
v___x_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_252_ = stack[0].m_num;
lean_object* v_a_253_ = stack[1].m_obj;
lean_object* v___y_254_ = stack[2].m_obj;
lean_object* v___y_255_ = stack[3].m_obj;
lean_object* v___y_256_ = stack[4].m_obj;
lean_object* v___y_257_ = stack[5].m_obj;
lean_object* v_res_299_;
v_res_299_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_252_, v_a_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
stack->m_obj
 = v_res_299_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg___boxed(lean_object* v___x_300_, lean_object* v_a_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
uint8_t v___x_13697__boxed_307_; lean_object* v_res_308_; 
v___x_13697__boxed_307_ = lean_unbox(v___x_300_);
v_res_308_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_13697__boxed_307_, v_a_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_308_;
}
}
lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0(lean_object* v_expr_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_317_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0));
v___x_318_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_314_);
v___x_319_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
v___x_320_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v___x_318_, v___x_319_);
lean_dec_ref(v___x_318_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_317_);
lean_ctor_set(v___x_321_, 1, v_expr_311_);
v___x_322_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_320_, v___x_321_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_331_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_331_ == 0)
{
v___x_325_ = v___x_322_;
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v___x_322_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v_fst_327_; lean_object* v___x_329_; 
v_fst_327_ = lean_ctor_get(v_a_323_, 0);
lean_inc(v_fst_327_);
lean_dec(v_a_323_);
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 0, v_fst_327_);
v___x_329_ = v___x_325_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_fst_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
else
{
lean_object* v_a_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_339_; 
v_a_332_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_339_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_339_ == 0)
{
v___x_334_ = v___x_322_;
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_a_332_);
lean_dec(v___x_322_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_339_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_337_; 
if (v_isShared_335_ == 0)
{
v___x_337_ = v___x_334_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_a_332_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_toDecl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_expr_311_ = stack[0].m_obj;
lean_object* v___y_312_ = stack[1].m_obj;
lean_object* v___y_313_ = stack[2].m_obj;
lean_object* v___y_314_ = stack[3].m_obj;
lean_object* v___y_315_ = stack[4].m_obj;
lean_object* v_res_340_;
v_res_340_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_expr_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___boxed(lean_object* v_expr_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_expr_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
return v_res_347_;
}
}
lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1(uint8_t v___x_348_, uint8_t v___x_349_, lean_object* v_xs_350_, lean_object* v_body_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_Meta_etaExpand(v_body_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; uint8_t v___x_359_; lean_object* v___x_360_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref_known(v___x_357_, 1);
v___x_359_ = 1;
v___x_360_ = l_Lean_Meta_mkLambdaFVars(v_xs_350_, v_a_358_, v___x_348_, v___x_349_, v___x_348_, v___x_349_, v___x_359_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
return v___x_360_;
}
else
{
return v___x_357_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_toDecl___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_348_ = stack[0].m_num;
uint8_t v___x_349_ = stack[1].m_num;
lean_object* v_xs_350_ = stack[2].m_obj;
lean_object* v_body_351_ = stack[3].m_obj;
lean_object* v___y_352_ = stack[4].m_obj;
lean_object* v___y_353_ = stack[5].m_obj;
lean_object* v___y_354_ = stack[6].m_obj;
lean_object* v___y_355_ = stack[7].m_obj;
lean_object* v_res_361_;
v_res_361_ = l_Lean_Compiler_LCNF_toDecl___lam__1(v___x_348_, v___x_349_, v_xs_350_, v_body_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
stack->m_obj
 = v_res_361_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1___boxed(lean_object* v___x_362_, lean_object* v___x_363_, lean_object* v_xs_364_, lean_object* v_body_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
uint8_t v___x_13938__boxed_371_; uint8_t v___x_13939__boxed_372_; lean_object* v_res_373_; 
v___x_13938__boxed_371_ = lean_unbox(v___x_362_);
v___x_13939__boxed_372_ = lean_unbox(v___x_363_);
v_res_373_ = l_Lean_Compiler_LCNF_toDecl___lam__1(v___x_13938__boxed_371_, v___x_13939__boxed_372_, v_xs_364_, v_body_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec_ref(v_xs_364_);
return v_res_373_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(lean_object* v_as_374_, size_t v_i_375_, size_t v_stop_376_){
_start:
{
uint8_t v___x_377_; 
v___x_377_ = lean_usize_dec_eq(v_i_375_, v_stop_376_);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; uint8_t v_borrow_379_; 
v___x_378_ = lean_array_uget_borrowed(v_as_374_, v_i_375_);
v_borrow_379_ = lean_ctor_get_uint8(v___x_378_, sizeof(void*)*3);
if (v_borrow_379_ == 0)
{
size_t v___x_380_; size_t v___x_381_; 
v___x_380_ = ((size_t)1ULL);
v___x_381_ = lean_usize_add(v_i_375_, v___x_380_);
v_i_375_ = v___x_381_;
goto _start;
}
else
{
return v_borrow_379_;
}
}
else
{
uint8_t v___x_383_; 
v___x_383_ = 0;
return v___x_383_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_374_ = stack[0].m_obj;
size_t v_i_375_ = stack[1].m_num;
size_t v_stop_376_ = stack[2].m_num;
uint8_t v_res_384_;
v_res_384_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_as_374_, v_i_375_, v_stop_376_);
stack->m_num = v_res_384_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3___boxed(lean_object* v_as_385_, lean_object* v_i_386_, lean_object* v_stop_387_){
_start:
{
size_t v_i_boxed_388_; size_t v_stop_boxed_389_; uint8_t v_res_390_; lean_object* v_r_391_; 
v_i_boxed_388_ = lean_unbox_usize(v_i_386_);
lean_dec(v_i_386_);
v_stop_boxed_389_ = lean_unbox_usize(v_stop_387_);
lean_dec(v_stop_387_);
v_res_390_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_as_385_, v_i_boxed_388_, v_stop_boxed_389_);
lean_dec_ref(v_as_385_);
v_r_391_ = lean_box(v_res_390_);
return v_r_391_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(uint8_t v___x_392_, size_t v_sz_393_, size_t v_i_394_, lean_object* v_bs_395_, lean_object* v___y_396_){
_start:
{
uint8_t v___x_398_; 
v___x_398_ = lean_usize_dec_lt(v_i_394_, v_sz_393_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; 
v___x_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_399_, 0, v_bs_395_);
return v___x_399_;
}
else
{
lean_object* v_v_400_; lean_object* v___x_401_; lean_object* v_bs_x27_402_; uint8_t v___x_403_; lean_object* v___x_404_; 
v_v_400_ = lean_array_uget(v_bs_395_, v_i_394_);
v___x_401_ = lean_unsigned_to_nat(0u);
v_bs_x27_402_ = lean_array_uset(v_bs_395_, v_i_394_, v___x_401_);
v___x_403_ = 0;
v___x_404_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v___x_403_, v_v_400_, v___x_392_, v___y_396_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; size_t v___x_406_; size_t v___x_407_; lean_object* v___x_408_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v___x_404_, 1);
v___x_406_ = ((size_t)1ULL);
v___x_407_ = lean_usize_add(v_i_394_, v___x_406_);
v___x_408_ = lean_array_uset(v_bs_x27_402_, v_i_394_, v_a_405_);
v_i_394_ = v___x_407_;
v_bs_395_ = v___x_408_;
goto _start;
}
else
{
lean_object* v_a_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_417_; 
lean_dec_ref(v_bs_x27_402_);
v_a_410_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_417_ == 0)
{
v___x_412_ = v___x_404_;
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_a_410_);
lean_dec(v___x_404_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_417_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_415_; 
if (v_isShared_413_ == 0)
{
v___x_415_ = v___x_412_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_a_410_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_392_ = stack[0].m_num;
size_t v_sz_393_ = stack[1].m_num;
size_t v_i_394_ = stack[2].m_num;
lean_object* v_bs_395_ = stack[3].m_obj;
lean_object* v___y_396_ = stack[4].m_obj;
lean_object* v_res_418_;
v_res_418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_392_, v_sz_393_, v_i_394_, v_bs_395_, v___y_396_);
stack->m_obj
 = v_res_418_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___boxed(lean_object* v___x_419_, lean_object* v_sz_420_, lean_object* v_i_421_, lean_object* v_bs_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
uint8_t v___x_14004__boxed_425_; size_t v_sz_boxed_426_; size_t v_i_boxed_427_; lean_object* v_res_428_; 
v___x_14004__boxed_425_ = lean_unbox(v___x_419_);
v_sz_boxed_426_ = lean_unbox_usize(v_sz_420_);
lean_dec(v_sz_420_);
v_i_boxed_427_ = lean_unbox_usize(v_i_421_);
lean_dec(v_i_421_);
v_res_428_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_14004__boxed_425_, v_sz_boxed_426_, v_i_boxed_427_, v_bs_422_, v___y_423_);
lean_dec(v___y_423_);
return v_res_428_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__1(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__0));
v___x_431_ = l_Lean_stringToMessageData(v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__3(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__2));
v___x_434_ = l_Lean_stringToMessageData(v___x_433_);
return v___x_434_;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_toDecl___closed__6(void){
_start:
{
lean_object* v___x_443_; uint64_t v___x_444_; 
v___x_443_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__5));
v___x_444_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_443_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__7(void){
_start:
{
uint64_t v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_uint64_once(&l_Lean_Compiler_LCNF_toDecl___closed__6, &l_Lean_Compiler_LCNF_toDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__6);
v___x_446_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__5));
v___x_447_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set_uint64(v___x_447_, sizeof(void*)*1, v___x_445_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__8(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0);
v___x_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__9(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_450_ = lean_unsigned_to_nat(32u);
v___x_451_ = lean_mk_empty_array_with_capacity(v___x_450_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__10(void){
_start:
{
size_t v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_453_ = ((size_t)5ULL);
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = lean_unsigned_to_nat(32u);
v___x_456_ = lean_mk_empty_array_with_capacity(v___x_455_);
v___x_457_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__9, &l_Lean_Compiler_LCNF_toDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__9);
v___x_458_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
lean_ctor_set(v___x_458_, 2, v___x_454_);
lean_ctor_set(v___x_458_, 3, v___x_454_);
lean_ctor_set_usize(v___x_458_, 4, v___x_453_);
return v___x_458_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__11(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_459_ = lean_box(1);
v___x_460_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_461_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_460_);
lean_ctor_set(v___x_462_, 2, v___x_459_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__13(void){
_start:
{
uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_465_ = 1;
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_box(0);
v___x_468_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__12));
v___x_469_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__11, &l_Lean_Compiler_LCNF_toDecl___closed__11_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__11);
v___x_470_ = lean_box(1);
v___x_471_ = 0;
v___x_472_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_473_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v___x_470_);
lean_ctor_set(v___x_473_, 2, v___x_469_);
lean_ctor_set(v___x_473_, 3, v___x_468_);
lean_ctor_set(v___x_473_, 4, v___x_467_);
lean_ctor_set(v___x_473_, 5, v___x_466_);
lean_ctor_set(v___x_473_, 6, v___x_467_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*7, v___x_471_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*7 + 1, v___x_471_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*7 + 2, v___x_471_);
lean_ctor_set_uint8(v___x_473_, sizeof(void*)*7 + 3, v___x_465_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__14(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_474_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_475_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
lean_ctor_set(v___x_477_, 2, v___x_476_);
lean_ctor_set(v___x_477_, 3, v___x_476_);
lean_ctor_set(v___x_477_, 4, v___x_475_);
lean_ctor_set(v___x_477_, 5, v___x_475_);
lean_ctor_set(v___x_477_, 6, v___x_475_);
lean_ctor_set(v___x_477_, 7, v___x_475_);
lean_ctor_set(v___x_477_, 8, v___x_475_);
lean_ctor_set(v___x_477_, 9, v___x_475_);
lean_ctor_set(v___x_477_, 10, v___x_475_);
lean_ctor_set(v___x_477_, 11, v___x_474_);
return v___x_477_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__15(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_479_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
lean_ctor_set(v___x_479_, 2, v___x_478_);
lean_ctor_set(v___x_479_, 3, v___x_478_);
lean_ctor_set(v___x_479_, 4, v___x_478_);
lean_ctor_set(v___x_479_, 5, v___x_478_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__16(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
lean_ctor_set(v___x_481_, 2, v___x_480_);
lean_ctor_set(v___x_481_, 3, v___x_480_);
lean_ctor_set(v___x_481_, 4, v___x_480_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__17(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_482_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__16, &l_Lean_Compiler_LCNF_toDecl___closed__16_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__16);
v___x_483_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_484_ = lean_box(1);
v___x_485_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__15, &l_Lean_Compiler_LCNF_toDecl___closed__15_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__15);
v___x_486_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__14, &l_Lean_Compiler_LCNF_toDecl___closed__14_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__14);
v___x_487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v___x_485_);
lean_ctor_set(v___x_487_, 2, v___x_484_);
lean_ctor_set(v___x_487_, 3, v___x_483_);
lean_ctor_set(v___x_487_, 4, v___x_482_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__19(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__18));
v___x_490_ = l_Lean_stringToMessageData(v___x_489_);
return v___x_490_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__21(void){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__20));
v___x_493_ = l_Lean_stringToMessageData(v___x_492_);
return v___x_493_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__23(void){
_start:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_495_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__22));
v___x_496_ = l_Lean_stringToMessageData(v___x_495_);
return v___x_496_;
}
}
lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object* v_declName_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_){
_start:
{
lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; uint8_t v___y_510_; lean_object* v___y_527_; lean_object* v___y_528_; uint8_t v___y_529_; lean_object* v_decl_530_; lean_object* v_name_531_; lean_object* v_params_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_546_; lean_object* v___y_547_; uint8_t v___y_548_; lean_object* v_decl_549_; lean_object* v___y_550_; lean_object* v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_598_; uint8_t v___y_599_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; uint8_t v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_617_; lean_object* v___y_618_; uint8_t v___y_619_; lean_object* v___y_620_; uint8_t v___y_621_; lean_object* v___y_622_; lean_object* v_a_623_; lean_object* v___y_646_; uint8_t v___y_647_; lean_object* v___y_648_; uint8_t v___y_649_; lean_object* v___y_650_; lean_object* v_a_651_; lean_object* v___x_673_; lean_object* v___y_675_; lean_object* v___x_827_; 
v___x_673_ = lean_box(1);
v___x_827_ = l_Lean_Compiler_isUnsafeRecName_x3f(v_declName_497_);
if (lean_obj_tag(v___x_827_) == 1)
{
lean_object* v_val_828_; 
lean_dec(v_declName_497_);
v_val_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_val_828_);
lean_dec_ref_known(v___x_827_, 1);
v___y_675_ = v_val_828_;
goto v___jp_674_;
}
else
{
lean_dec(v___x_827_);
v___y_675_ = v_declName_497_;
goto v___jp_674_;
}
v___jp_503_:
{
if (v___y_510_ == 0)
{
lean_object* v___x_511_; 
lean_dec(v___y_504_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___y_505_);
return v___x_511_;
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v_a_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_525_; 
lean_dec_ref(v___y_505_);
v___x_512_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__1, &l_Lean_Compiler_LCNF_toDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__1);
v___x_513_ = l_Lean_MessageData_ofName(v___y_504_);
v___x_514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__3, &l_Lean_Compiler_LCNF_toDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__3);
v___x_516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_514_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v___x_516_, v___y_509_, v___y_507_, v___y_506_, v___y_508_);
v_a_518_ = lean_ctor_get(v___x_517_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_517_);
if (v_isSharedCheck_525_ == 0)
{
v___x_520_ = v___x_517_;
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_a_518_);
lean_dec(v___x_517_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_525_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_a_518_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
}
}
v___jp_526_:
{
uint8_t v___x_537_; 
lean_inc(v_name_531_);
v___x_537_ = l_Lean_isExport(v___y_528_, v_name_531_);
if (v___x_537_ == 0)
{
lean_dec_ref(v_params_532_);
v___y_504_ = v_name_531_;
v___y_505_ = v_decl_530_;
v___y_506_ = v___y_535_;
v___y_507_ = v___y_534_;
v___y_508_ = v___y_536_;
v___y_509_ = v___y_533_;
v___y_510_ = v___y_529_;
goto v___jp_503_;
}
else
{
lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_538_ = lean_array_get_size(v_params_532_);
v___x_539_ = lean_nat_dec_lt(v___y_527_, v___x_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
lean_dec_ref(v_params_532_);
lean_dec(v_name_531_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v_decl_530_);
return v___x_540_;
}
else
{
if (v___x_539_ == 0)
{
lean_object* v___x_541_; 
lean_dec_ref(v_params_532_);
lean_dec(v_name_531_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v_decl_530_);
return v___x_541_;
}
else
{
size_t v___x_542_; size_t v___x_543_; uint8_t v___x_544_; 
v___x_542_ = ((size_t)0ULL);
v___x_543_ = lean_usize_of_nat(v___x_538_);
v___x_544_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_params_532_, v___x_542_, v___x_543_);
lean_dec_ref(v_params_532_);
v___y_504_ = v_name_531_;
v___y_505_ = v_decl_530_;
v___y_506_ = v___y_535_;
v___y_507_ = v___y_534_;
v___y_508_ = v___y_536_;
v___y_509_ = v___y_533_;
v___y_510_ = v___x_544_;
goto v___jp_503_;
}
}
}
}
v___jp_545_:
{
lean_object* v___x_554_; 
v___x_554_ = l_Lean_Compiler_LCNF_Decl_etaExpand(v_decl_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v_a_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_a_555_ = lean_ctor_get(v___x_554_, 0);
lean_inc(v_a_555_);
lean_dec_ref_known(v___x_554_, 1);
v___x_556_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_552_);
v___x_557_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
v___x_558_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v___x_556_, v___x_557_);
lean_dec_ref(v___x_556_);
if (v___x_558_ == 0)
{
lean_object* v_toSignature_559_; lean_object* v_name_560_; lean_object* v_params_561_; 
v_toSignature_559_ = lean_ctor_get(v_a_555_, 0);
v_name_560_ = lean_ctor_get(v_toSignature_559_, 0);
lean_inc(v_name_560_);
v_params_561_ = lean_ctor_get(v_toSignature_559_, 3);
lean_inc_ref(v_params_561_);
v___y_527_ = v___y_547_;
v___y_528_ = v___y_546_;
v___y_529_ = v___y_548_;
v_decl_530_ = v_a_555_;
v_name_531_ = v_name_560_;
v_params_532_ = v_params_561_;
v___y_533_ = v___y_550_;
v___y_534_ = v___y_551_;
v___y_535_ = v___y_552_;
v___y_536_ = v___y_553_;
goto v___jp_526_;
}
else
{
lean_object* v_toSignature_562_; lean_object* v_value_563_; uint8_t v_recursive_564_; lean_object* v_inlineAttr_x3f_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_596_; 
v_toSignature_562_ = lean_ctor_get(v_a_555_, 0);
v_value_563_ = lean_ctor_get(v_a_555_, 1);
v_recursive_564_ = lean_ctor_get_uint8(v_a_555_, sizeof(void*)*3);
v_inlineAttr_x3f_565_ = lean_ctor_get(v_a_555_, 2);
v_isSharedCheck_596_ = !lean_is_exclusive(v_a_555_);
if (v_isSharedCheck_596_ == 0)
{
v___x_567_ = v_a_555_;
v_isShared_568_ = v_isSharedCheck_596_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_inlineAttr_x3f_565_);
lean_inc(v_value_563_);
lean_inc(v_toSignature_562_);
lean_dec(v_a_555_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_596_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v_name_569_; lean_object* v_levelParams_570_; lean_object* v_type_571_; lean_object* v_params_572_; uint8_t v_safe_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_595_; 
v_name_569_ = lean_ctor_get(v_toSignature_562_, 0);
v_levelParams_570_ = lean_ctor_get(v_toSignature_562_, 1);
v_type_571_ = lean_ctor_get(v_toSignature_562_, 2);
v_params_572_ = lean_ctor_get(v_toSignature_562_, 3);
v_safe_573_ = lean_ctor_get_uint8(v_toSignature_562_, sizeof(void*)*4);
v_isSharedCheck_595_ = !lean_is_exclusive(v_toSignature_562_);
if (v_isSharedCheck_595_ == 0)
{
v___x_575_ = v_toSignature_562_;
v_isShared_576_ = v_isSharedCheck_595_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_params_572_);
lean_inc(v_type_571_);
lean_inc(v_levelParams_570_);
lean_inc(v_name_569_);
lean_dec(v_toSignature_562_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_595_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
size_t v_sz_577_; size_t v___x_578_; lean_object* v___x_579_; 
v_sz_577_ = lean_array_size(v_params_572_);
v___x_578_ = ((size_t)0ULL);
v___x_579_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___y_548_, v_sz_577_, v___x_578_, v_params_572_, v___y_551_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_582_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc_n(v_a_580_, 2);
lean_dec_ref_known(v___x_579_, 1);
lean_inc(v_name_569_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 3, v_a_580_);
v___x_582_ = v___x_575_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_name_569_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_levelParams_570_);
lean_ctor_set(v_reuseFailAlloc_586_, 2, v_type_571_);
lean_ctor_set(v_reuseFailAlloc_586_, 3, v_a_580_);
lean_ctor_set_uint8(v_reuseFailAlloc_586_, sizeof(void*)*4, v_safe_573_);
v___x_582_ = v_reuseFailAlloc_586_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_584_; 
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_582_);
v___x_584_ = v___x_567_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_value_563_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_inlineAttr_x3f_565_);
lean_ctor_set_uint8(v_reuseFailAlloc_585_, sizeof(void*)*3, v_recursive_564_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
v___y_527_ = v___y_547_;
v___y_528_ = v___y_546_;
v___y_529_ = v___y_548_;
v_decl_530_ = v___x_584_;
v_name_531_ = v_name_569_;
v_params_532_ = v_a_580_;
v___y_533_ = v___y_550_;
v___y_534_ = v___y_551_;
v___y_535_ = v___y_552_;
v___y_536_ = v___y_553_;
goto v___jp_526_;
}
}
}
else
{
lean_object* v_a_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_594_; 
lean_del_object(v___x_575_);
lean_dec_ref(v_type_571_);
lean_dec(v_levelParams_570_);
lean_dec(v_name_569_);
lean_del_object(v___x_567_);
lean_dec(v_inlineAttr_x3f_565_);
lean_dec_ref(v_value_563_);
lean_dec_ref(v___y_546_);
v_a_587_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_594_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_594_ == 0)
{
v___x_589_ = v___x_579_;
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_a_587_);
lean_dec(v___x_579_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_594_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_592_; 
if (v_isShared_590_ == 0)
{
v___x_592_ = v___x_589_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_546_);
return v___x_554_;
}
}
v___jp_597_:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_611_ = l_Lean_ConstantInfo_levelParams(v___y_600_);
lean_dec_ref(v___y_600_);
v___x_612_ = lean_mk_empty_array_with_capacity(v___y_602_);
v___x_613_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_613_, 0, v___y_598_);
lean_ctor_set(v___x_613_, 1, v___x_611_);
lean_ctor_set(v___x_613_, 2, v___y_605_);
lean_ctor_set(v___x_613_, 3, v___x_612_);
lean_ctor_set_uint8(v___x_613_, sizeof(void*)*4, v___y_599_);
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v___y_604_);
v___x_615_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
lean_ctor_set(v___x_615_, 2, v___y_606_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*3, v___y_603_);
v___y_546_ = v___y_601_;
v___y_547_ = v___y_602_;
v___y_548_ = v___y_603_;
v_decl_549_ = v___x_615_;
v___y_550_ = v___y_607_;
v___y_551_ = v___y_608_;
v___y_552_ = v___y_609_;
v___y_553_ = v___y_610_;
goto v___jp_545_;
}
v___jp_616_:
{
lean_object* v___x_624_; 
lean_inc_ref(v_a_623_);
v___x_624_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_a_623_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
if (lean_obj_tag(v___x_624_) == 0)
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_636_; 
v_a_625_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_636_ == 0)
{
v___x_627_ = v___x_624_;
v_isShared_628_ = v_isSharedCheck_636_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_624_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_636_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_629_ = l_Lean_ConstantInfo_levelParams(v___y_620_);
lean_dec_ref(v___y_620_);
v___x_630_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_630_, 0, v___y_618_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
lean_ctor_set(v___x_630_, 2, v_a_623_);
lean_ctor_set(v___x_630_, 3, v_a_625_);
lean_ctor_set_uint8(v___x_630_, sizeof(void*)*4, v___y_619_);
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v___y_617_);
v___x_632_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_632_, 0, v___x_630_);
lean_ctor_set(v___x_632_, 1, v___x_631_);
lean_ctor_set(v___x_632_, 2, v___y_622_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*3, v___y_621_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_632_);
v___x_634_ = v___x_627_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
else
{
lean_object* v_a_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_644_; 
lean_dec_ref(v_a_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_620_);
lean_dec(v___y_618_);
lean_dec(v___y_617_);
v_a_637_ = lean_ctor_get(v___x_624_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_644_ == 0)
{
v___x_639_ = v___x_624_;
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_a_637_);
lean_dec(v___x_624_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_644_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_642_; 
if (v_isShared_640_ == 0)
{
v___x_642_ = v___x_639_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
v___jp_645_:
{
lean_object* v___x_652_; 
lean_inc_ref(v_a_651_);
v___x_652_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_a_651_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
if (lean_obj_tag(v___x_652_) == 0)
{
lean_object* v_a_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_664_; 
v_a_653_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_664_ == 0)
{
v___x_655_ = v___x_652_;
v_isShared_656_ = v_isSharedCheck_664_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_a_653_);
lean_dec(v___x_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_664_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_657_ = l_Lean_ConstantInfo_levelParams(v___y_648_);
lean_dec_ref(v___y_648_);
v___x_658_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_658_, 0, v___y_646_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
lean_ctor_set(v___x_658_, 2, v_a_651_);
lean_ctor_set(v___x_658_, 3, v_a_653_);
lean_ctor_set_uint8(v___x_658_, sizeof(void*)*4, v___y_647_);
v___x_659_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__4));
v___x_660_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_660_, 0, v___x_658_);
lean_ctor_set(v___x_660_, 1, v___x_659_);
lean_ctor_set(v___x_660_, 2, v___y_650_);
lean_ctor_set_uint8(v___x_660_, sizeof(void*)*3, v___y_649_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_660_);
v___x_662_ = v___x_655_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v_a_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_648_);
lean_dec(v___y_646_);
v_a_665_ = lean_ctor_get(v___x_652_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_652_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_652_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_652_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
v___jp_674_:
{
lean_object* v___x_676_; lean_object* v_a_677_; 
lean_inc(v___y_675_);
v___x_676_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v___y_675_, v_a_501_);
v_a_677_ = lean_ctor_get(v___x_676_, 0);
lean_inc(v_a_677_);
lean_dec_ref(v___x_676_);
if (lean_obj_tag(v_a_677_) == 1)
{
lean_object* v_val_678_; lean_object* v___x_679_; lean_object* v_a_680_; lean_object* v___x_681_; lean_object* v_env_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_val_678_ = lean_ctor_get(v_a_677_, 0);
lean_inc(v_val_678_);
lean_dec_ref_known(v_a_677_, 1);
lean_inc_n(v___y_675_, 3);
v___x_679_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v___y_675_, v_a_501_);
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref(v___x_679_);
v___x_681_ = lean_st_ref_get(v_a_501_);
v_env_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc_ref_n(v_env_682_, 3);
lean_dec(v___x_681_);
v___x_683_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_682_, v___y_675_);
v___x_684_ = l_Lean_getExternAttrData_x3f(v_env_682_, v___y_675_);
if (lean_obj_tag(v___x_684_) == 1)
{
lean_object* v_val_685_; lean_object* v___x_686_; uint8_t v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec_ref(v_env_682_);
v_val_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_val_685_);
lean_dec_ref_known(v___x_684_, 1);
v___x_686_ = l_Lean_ConstantInfo_type(v_val_678_);
v___x_687_ = 0;
v___x_688_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__13, &l_Lean_Compiler_LCNF_toDecl___closed__13_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__13);
v___x_689_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__17, &l_Lean_Compiler_LCNF_toDecl___closed__17_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__17);
v___x_690_ = lean_st_mk_ref(v___x_689_);
v___x_691_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_686_, v___x_688_, v___x_690_, v_a_500_, v_a_501_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_a_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_692_);
lean_dec_ref_known(v___x_691_, 1);
v___x_693_ = lean_st_ref_get(v___x_690_);
lean_dec(v___x_690_);
lean_dec(v___x_693_);
v___x_694_ = lean_unbox(v_a_680_);
lean_dec(v_a_680_);
v___y_617_ = v_val_685_;
v___y_618_ = v___y_675_;
v___y_619_ = v___x_694_;
v___y_620_ = v_val_678_;
v___y_621_ = v___x_687_;
v___y_622_ = v___x_683_;
v_a_623_ = v_a_692_;
goto v___jp_616_;
}
else
{
lean_dec(v___x_690_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v_a_695_; uint8_t v___x_696_; 
v_a_695_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_691_, 1);
v___x_696_ = lean_unbox(v_a_680_);
lean_dec(v_a_680_);
v___y_617_ = v_val_685_;
v___y_618_ = v___y_675_;
v___y_619_ = v___x_696_;
v___y_620_ = v_val_678_;
v___y_621_ = v___x_687_;
v___y_622_ = v___x_683_;
v_a_623_ = v_a_695_;
goto v___jp_616_;
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_dec(v_val_685_);
lean_dec(v___x_683_);
lean_dec(v_a_680_);
lean_dec(v_val_678_);
lean_dec(v___y_675_);
v_a_697_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_691_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_691_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
else
{
uint8_t v___x_705_; uint8_t v___x_706_; 
lean_dec(v___x_684_);
lean_inc(v___y_675_);
lean_inc_ref(v_env_682_);
v___x_705_ = lean_has_init_attr(v_env_682_, v___y_675_);
v___x_706_ = 1;
if (v___x_705_ == 0)
{
lean_object* v___x_707_; 
lean_inc(v_val_678_);
v___x_707_ = l_Lean_ConstantInfo_value_x3f(v_val_678_, v___x_706_);
if (lean_obj_tag(v___x_707_) == 1)
{
lean_object* v_val_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___f_711_; lean_object* v___x_712_; uint8_t v___x_713_; uint8_t v___x_714_; uint8_t v___x_715_; lean_object* v___x_716_; uint64_t v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v_val_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_val_708_);
lean_dec_ref_known(v___x_707_, 1);
v___x_709_ = lean_box(v___x_705_);
v___x_710_ = lean_box(v___x_706_);
v___f_711_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lam__1___boxed), 9, 2);
lean_closure_set(v___f_711_, 0, v___x_709_);
lean_closure_set(v___f_711_, 1, v___x_710_);
v___x_712_ = l_Lean_ConstantInfo_type(v_val_678_);
v___x_713_ = 1;
v___x_714_ = 0;
v___x_715_ = 2;
v___x_716_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_716_, 0, v___x_705_);
lean_ctor_set_uint8(v___x_716_, 1, v___x_705_);
lean_ctor_set_uint8(v___x_716_, 2, v___x_705_);
lean_ctor_set_uint8(v___x_716_, 3, v___x_705_);
lean_ctor_set_uint8(v___x_716_, 4, v___x_705_);
lean_ctor_set_uint8(v___x_716_, 5, v___x_706_);
lean_ctor_set_uint8(v___x_716_, 6, v___x_706_);
lean_ctor_set_uint8(v___x_716_, 7, v___x_705_);
lean_ctor_set_uint8(v___x_716_, 8, v___x_706_);
lean_ctor_set_uint8(v___x_716_, 9, v___x_713_);
lean_ctor_set_uint8(v___x_716_, 10, v___x_714_);
lean_ctor_set_uint8(v___x_716_, 11, v___x_706_);
lean_ctor_set_uint8(v___x_716_, 12, v___x_706_);
lean_ctor_set_uint8(v___x_716_, 13, v___x_706_);
lean_ctor_set_uint8(v___x_716_, 14, v___x_715_);
lean_ctor_set_uint8(v___x_716_, 15, v___x_706_);
lean_ctor_set_uint8(v___x_716_, 16, v___x_706_);
lean_ctor_set_uint8(v___x_716_, 17, v___x_706_);
lean_ctor_set_uint8(v___x_716_, 18, v___x_706_);
lean_ctor_set_uint8(v___x_716_, 19, v___x_705_);
v___x_717_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_716_);
v___x_718_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_718_, 0, v___x_716_);
lean_ctor_set_uint64(v___x_718_, sizeof(void*)*1, v___x_717_);
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__11, &l_Lean_Compiler_LCNF_toDecl___closed__11_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__11);
v___x_721_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__12));
v___x_722_ = lean_box(0);
v___x_723_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_723_, 0, v___x_718_);
lean_ctor_set(v___x_723_, 1, v___x_673_);
lean_ctor_set(v___x_723_, 2, v___x_720_);
lean_ctor_set(v___x_723_, 3, v___x_721_);
lean_ctor_set(v___x_723_, 4, v___x_722_);
lean_ctor_set(v___x_723_, 5, v___x_719_);
lean_ctor_set(v___x_723_, 6, v___x_722_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*7, v___x_705_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*7 + 1, v___x_705_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*7 + 2, v___x_705_);
lean_ctor_set_uint8(v___x_723_, sizeof(void*)*7 + 3, v___x_706_);
v___x_724_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__17, &l_Lean_Compiler_LCNF_toDecl___closed__17_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__17);
v___x_725_ = lean_st_mk_ref(v___x_724_);
v___x_726_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_712_, v___x_723_, v___x_725_, v_a_500_, v_a_501_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_728_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref_known(v___x_726_, 1);
v___x_728_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_val_708_, v___f_711_, v___x_705_, v___x_723_, v___x_725_, v_a_500_, v_a_501_);
lean_dec_ref_known(v___x_723_, 7);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v_a_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_a_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_a_729_);
lean_dec_ref_known(v___x_728_, 1);
v___x_730_ = lean_st_ref_get(v___x_725_);
lean_dec(v___x_725_);
lean_dec(v___x_730_);
lean_inc(v_a_727_);
v___x_731_ = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(v_a_729_, v_a_727_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_731_, 1);
if (lean_obj_tag(v_a_732_) == 1)
{
lean_object* v_k_733_; 
v_k_733_ = lean_ctor_get(v_a_732_, 1);
lean_inc_ref(v_k_733_);
if (lean_obj_tag(v_k_733_) == 5)
{
lean_object* v_decl_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_757_; 
v_decl_734_ = lean_ctor_get(v_a_732_, 0);
lean_inc_ref(v_decl_734_);
lean_dec_ref_known(v_a_732_, 2);
v_isSharedCheck_757_ = !lean_is_exclusive(v_k_733_);
if (v_isSharedCheck_757_ == 0)
{
lean_object* v_unused_758_; 
v_unused_758_ = lean_ctor_get(v_k_733_, 0);
lean_dec(v_unused_758_);
v___x_736_ = v_k_733_;
v_isShared_737_ = v_isSharedCheck_757_;
goto v_resetjp_735_;
}
else
{
lean_dec(v_k_733_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_757_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
uint8_t v___x_738_; lean_object* v___x_739_; 
v___x_738_ = 0;
v___x_739_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_738_, v_decl_734_, v___x_705_, v_a_499_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_params_740_; lean_object* v_value_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; lean_object* v___x_746_; 
lean_dec_ref_known(v___x_739_, 1);
v_params_740_ = lean_ctor_get(v_decl_734_, 2);
lean_inc_ref(v_params_740_);
v_value_741_ = lean_ctor_get(v_decl_734_, 4);
lean_inc_ref(v_value_741_);
lean_dec_ref(v_decl_734_);
v___x_742_ = l_Lean_ConstantInfo_levelParams(v_val_678_);
lean_dec(v_val_678_);
v___x_743_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_743_, 0, v___y_675_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
lean_ctor_set(v___x_743_, 2, v_a_727_);
lean_ctor_set(v___x_743_, 3, v_params_740_);
v___x_744_ = lean_unbox(v_a_680_);
lean_dec(v_a_680_);
lean_ctor_set_uint8(v___x_743_, sizeof(void*)*4, v___x_744_);
if (v_isShared_737_ == 0)
{
lean_ctor_set_tag(v___x_736_, 0);
lean_ctor_set(v___x_736_, 0, v_value_741_);
v___x_746_ = v___x_736_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_value_741_);
v___x_746_ = v_reuseFailAlloc_748_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
lean_object* v___x_747_; 
v___x_747_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_747_, 0, v___x_743_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
lean_ctor_set(v___x_747_, 2, v___x_683_);
lean_ctor_set_uint8(v___x_747_, sizeof(void*)*3, v___x_705_);
v___y_546_ = v_env_682_;
v___y_547_ = v___x_719_;
v___y_548_ = v___x_705_;
v_decl_549_ = v___x_747_;
v___y_550_ = v_a_498_;
v___y_551_ = v_a_499_;
v___y_552_ = v_a_500_;
v___y_553_ = v_a_501_;
goto v___jp_545_;
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_del_object(v___x_736_);
lean_dec_ref(v_decl_734_);
lean_dec(v_a_727_);
lean_dec(v___x_683_);
lean_dec_ref(v_env_682_);
lean_dec(v_a_680_);
lean_dec(v_val_678_);
lean_dec(v___y_675_);
v_a_749_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_739_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_739_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
else
{
uint8_t v___x_759_; 
lean_dec_ref(v_k_733_);
v___x_759_ = lean_unbox(v_a_680_);
lean_dec(v_a_680_);
v___y_598_ = v___y_675_;
v___y_599_ = v___x_759_;
v___y_600_ = v_val_678_;
v___y_601_ = v_env_682_;
v___y_602_ = v___x_719_;
v___y_603_ = v___x_705_;
v___y_604_ = v_a_732_;
v___y_605_ = v_a_727_;
v___y_606_ = v___x_683_;
v___y_607_ = v_a_498_;
v___y_608_ = v_a_499_;
v___y_609_ = v_a_500_;
v___y_610_ = v_a_501_;
goto v___jp_597_;
}
}
else
{
uint8_t v___x_760_; 
v___x_760_ = lean_unbox(v_a_680_);
lean_dec(v_a_680_);
v___y_598_ = v___y_675_;
v___y_599_ = v___x_760_;
v___y_600_ = v_val_678_;
v___y_601_ = v_env_682_;
v___y_602_ = v___x_719_;
v___y_603_ = v___x_705_;
v___y_604_ = v_a_732_;
v___y_605_ = v_a_727_;
v___y_606_ = v___x_683_;
v___y_607_ = v_a_498_;
v___y_608_ = v_a_499_;
v___y_609_ = v_a_500_;
v___y_610_ = v_a_501_;
goto v___jp_597_;
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec(v_a_727_);
lean_dec(v___x_683_);
lean_dec_ref(v_env_682_);
lean_dec(v_a_680_);
lean_dec(v_val_678_);
lean_dec(v___y_675_);
v_a_761_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_731_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_731_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec(v_a_727_);
lean_dec(v___x_725_);
lean_dec(v___x_683_);
lean_dec_ref(v_env_682_);
lean_dec(v_a_680_);
lean_dec(v_val_678_);
lean_dec(v___y_675_);
v_a_769_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_728_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_728_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec(v___x_725_);
lean_dec_ref_known(v___x_723_, 7);
lean_dec_ref(v___f_711_);
lean_dec(v_val_708_);
lean_dec(v___x_683_);
lean_dec_ref(v_env_682_);
lean_dec(v_a_680_);
lean_dec(v_val_678_);
lean_dec(v___y_675_);
v_a_777_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_726_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_726_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
lean_dec(v___x_707_);
lean_dec(v___x_683_);
lean_dec_ref(v_env_682_);
lean_dec(v_a_680_);
lean_dec(v_val_678_);
v___x_785_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__19, &l_Lean_Compiler_LCNF_toDecl___closed__19_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__19);
v___x_786_ = l_Lean_MessageData_ofConstName(v___y_675_, v___x_705_);
v___x_787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_785_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__21, &l_Lean_Compiler_LCNF_toDecl___closed__21_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__21);
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_787_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v___x_789_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
return v___x_790_;
}
}
else
{
lean_object* v___x_791_; uint8_t v___x_792_; uint8_t v___x_793_; uint8_t v___x_794_; uint8_t v___x_795_; lean_object* v___x_796_; uint64_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec_ref(v_env_682_);
v___x_791_ = l_Lean_ConstantInfo_type(v_val_678_);
v___x_792_ = 0;
v___x_793_ = 1;
v___x_794_ = 0;
v___x_795_ = 2;
v___x_796_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_796_, 0, v___x_792_);
lean_ctor_set_uint8(v___x_796_, 1, v___x_792_);
lean_ctor_set_uint8(v___x_796_, 2, v___x_792_);
lean_ctor_set_uint8(v___x_796_, 3, v___x_792_);
lean_ctor_set_uint8(v___x_796_, 4, v___x_792_);
lean_ctor_set_uint8(v___x_796_, 5, v___x_705_);
lean_ctor_set_uint8(v___x_796_, 6, v___x_705_);
lean_ctor_set_uint8(v___x_796_, 7, v___x_792_);
lean_ctor_set_uint8(v___x_796_, 8, v___x_705_);
lean_ctor_set_uint8(v___x_796_, 9, v___x_793_);
lean_ctor_set_uint8(v___x_796_, 10, v___x_794_);
lean_ctor_set_uint8(v___x_796_, 11, v___x_705_);
lean_ctor_set_uint8(v___x_796_, 12, v___x_705_);
lean_ctor_set_uint8(v___x_796_, 13, v___x_705_);
lean_ctor_set_uint8(v___x_796_, 14, v___x_795_);
lean_ctor_set_uint8(v___x_796_, 15, v___x_705_);
lean_ctor_set_uint8(v___x_796_, 16, v___x_705_);
lean_ctor_set_uint8(v___x_796_, 17, v___x_705_);
lean_ctor_set_uint8(v___x_796_, 18, v___x_705_);
lean_ctor_set_uint8(v___x_796_, 19, v___x_792_);
v___x_797_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_798_, 0, v___x_796_);
lean_ctor_set_uint64(v___x_798_, sizeof(void*)*1, v___x_797_);
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__11, &l_Lean_Compiler_LCNF_toDecl___closed__11_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__11);
v___x_801_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__12));
v___x_802_ = lean_box(0);
v___x_803_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_803_, 0, v___x_798_);
lean_ctor_set(v___x_803_, 1, v___x_673_);
lean_ctor_set(v___x_803_, 2, v___x_800_);
lean_ctor_set(v___x_803_, 3, v___x_801_);
lean_ctor_set(v___x_803_, 4, v___x_802_);
lean_ctor_set(v___x_803_, 5, v___x_799_);
lean_ctor_set(v___x_803_, 6, v___x_802_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*7, v___x_792_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*7 + 1, v___x_792_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*7 + 2, v___x_792_);
lean_ctor_set_uint8(v___x_803_, sizeof(void*)*7 + 3, v___x_706_);
v___x_804_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__17, &l_Lean_Compiler_LCNF_toDecl___closed__17_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__17);
v___x_805_ = lean_st_mk_ref(v___x_804_);
v___x_806_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_791_, v___x_803_, v___x_805_, v_a_500_, v_a_501_);
lean_dec_ref_known(v___x_803_, 7);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v___x_806_, 1);
v___x_808_ = lean_st_ref_get(v___x_805_);
lean_dec(v___x_805_);
lean_dec(v___x_808_);
v___x_809_ = lean_unbox(v_a_680_);
lean_dec(v_a_680_);
v___y_646_ = v___y_675_;
v___y_647_ = v___x_809_;
v___y_648_ = v_val_678_;
v___y_649_ = v___x_792_;
v___y_650_ = v___x_683_;
v_a_651_ = v_a_807_;
goto v___jp_645_;
}
else
{
lean_dec(v___x_805_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_810_; uint8_t v___x_811_; 
v_a_810_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_810_);
lean_dec_ref_known(v___x_806_, 1);
v___x_811_ = lean_unbox(v_a_680_);
lean_dec(v_a_680_);
v___y_646_ = v___y_675_;
v___y_647_ = v___x_811_;
v___y_648_ = v_val_678_;
v___y_649_ = v___x_792_;
v___y_650_ = v___x_683_;
v_a_651_ = v_a_810_;
goto v___jp_645_;
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v___x_683_);
lean_dec(v_a_680_);
lean_dec(v_val_678_);
lean_dec(v___y_675_);
v_a_812_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_806_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_806_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_820_; uint8_t v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
lean_dec(v_a_677_);
v___x_820_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__19, &l_Lean_Compiler_LCNF_toDecl___closed__19_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__19);
v___x_821_ = 0;
v___x_822_ = l_Lean_MessageData_ofConstName(v___y_675_, v___x_821_);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_820_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__23, &l_Lean_Compiler_LCNF_toDecl___closed__23_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__23);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v___x_825_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
return v___x_826_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_toDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_497_ = stack[0].m_obj;
lean_object* v_a_498_ = stack[1].m_obj;
lean_object* v_a_499_ = stack[2].m_obj;
lean_object* v_a_500_ = stack[3].m_obj;
lean_object* v_a_501_ = stack[4].m_obj;
lean_object* v_res_829_;
v_res_829_ = l_Lean_Compiler_LCNF_toDecl(v_declName_497_, v_a_498_, v_a_499_, v_a_500_, v_a_501_);
stack->m_obj
 = v_res_829_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___boxed(lean_object* v_declName_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_Compiler_LCNF_toDecl(v_declName_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
return v_res_836_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(uint8_t v___x_837_, lean_object* v_inst_838_, lean_object* v_a_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_837_, v_a_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
return v___x_845_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_837_ = stack[0].m_num;
lean_object* v_a_839_ = stack[2].m_obj;
lean_object* v___y_840_ = stack[3].m_obj;
lean_object* v___y_841_ = stack[4].m_obj;
lean_object* v___y_842_ = stack[5].m_obj;
lean_object* v___y_843_ = stack[6].m_obj;
lean_object* v_res_846_;
v_res_846_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(v___x_837_, lean_box(0), v_a_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
stack->m_obj
 = v_res_846_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___boxed(lean_object* v___x_847_, lean_object* v_inst_848_, lean_object* v_a_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
uint8_t v___x_15462__boxed_855_; lean_object* v_res_856_; 
v___x_15462__boxed_855_ = lean_unbox(v___x_847_);
v_res_856_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(v___x_15462__boxed_855_, v_inst_848_, v_a_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
return v_res_856_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4(uint8_t v___x_857_, size_t v_sz_858_, size_t v_i_859_, lean_object* v_bs_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_857_, v_sz_858_, v_i_859_, v_bs_860_, v___y_862_);
return v___x_866_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_857_ = stack[0].m_num;
size_t v_sz_858_ = stack[1].m_num;
size_t v_i_859_ = stack[2].m_num;
lean_object* v_bs_860_ = stack[3].m_obj;
lean_object* v___y_861_ = stack[4].m_obj;
lean_object* v___y_862_ = stack[5].m_obj;
lean_object* v___y_863_ = stack[6].m_obj;
lean_object* v___y_864_ = stack[7].m_obj;
lean_object* v_res_867_;
v_res_867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4(v___x_857_, v_sz_858_, v_i_859_, v_bs_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
stack->m_obj
 = v_res_867_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___boxed(lean_object* v___x_868_, lean_object* v_sz_869_, lean_object* v_i_870_, lean_object* v_bs_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
uint8_t v___x_15500__boxed_877_; size_t v_sz_boxed_878_; size_t v_i_boxed_879_; lean_object* v_res_880_; 
v___x_15500__boxed_877_ = lean_unbox(v___x_868_);
v_sz_boxed_878_ = lean_unbox_usize(v_sz_869_);
lean_dec(v_sz_869_);
v_i_boxed_879_ = lean_unbox_usize(v_i_870_);
lean_dec(v_i_870_);
v_res_880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4(v___x_15500__boxed_877_, v_sz_boxed_878_, v_i_boxed_879_, v_bs_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
return v_res_880_;
}
}
lean_object* runtime_initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_ToLCNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ExportAttr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ToDecl(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToLCNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ExportAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ToDecl(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_ToLCNF(uint8_t builtin);
lean_object* initialize_Lean_Compiler_Options(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_MatcherInfo(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ExportAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToDecl(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_InitAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToLCNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Options(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ExportAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ToDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ToDecl(builtin);
}
#ifdef __cplusplus
}
#endif
