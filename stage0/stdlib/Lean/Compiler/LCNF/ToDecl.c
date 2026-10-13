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
uint8_t l_Lean_hasInitAttr(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(lean_object* v_declName_1_, lean_object* v_a_2_){
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg___boxed(lean_object* v_declName_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v_declName_12_, v_a_13_);
lean_dec(v_a_13_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f(lean_object* v_declName_16_, lean_object* v_a_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v_declName_16_, v_a_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getDeclInfo_x3f___boxed(lean_object* v_declName_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f(v_declName_21_, v_a_22_, v_a_23_);
lean_dec(v_a_23_);
lean_dec_ref(v_a_22_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(lean_object* v_declName_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___x_29_; lean_object* v_env_30_; uint8_t v___x_31_; lean_object* v___x_32_; 
v___x_29_ = lean_st_ref_get(v_a_27_);
v_env_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc_ref_n(v_env_30_, 2);
lean_dec(v___x_29_);
v___x_31_ = 0;
lean_inc(v_declName_26_);
v___x_32_ = l_Lean_Environment_find_x3f(v_env_30_, v_declName_26_, v___x_31_);
if (lean_obj_tag(v___x_32_) == 1)
{
lean_object* v_val_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_60_; 
v_val_33_ = lean_ctor_get(v___x_32_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_32_);
if (v_isSharedCheck_60_ == 0)
{
v___x_35_ = v___x_32_;
v_isShared_36_ = v_isSharedCheck_60_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_val_33_);
lean_dec(v___x_32_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_60_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
uint8_t v___x_37_; uint8_t v___y_39_; 
v___x_37_ = l_Lean_ConstantInfo_isUnsafe(v_val_33_);
if (v___x_37_ == 0)
{
uint8_t v___x_55_; 
v___x_55_ = 1;
if (lean_obj_tag(v_val_33_) == 3)
{
lean_dec_ref_known(v_val_33_, 1);
v___y_39_ = v___x_55_;
goto v___jp_38_;
}
else
{
lean_dec(v_val_33_);
if (v___x_37_ == 0)
{
lean_object* v___x_56_; lean_object* v___x_57_; 
lean_del_object(v___x_35_);
lean_dec_ref(v_env_30_);
lean_dec(v_declName_26_);
v___x_56_ = lean_box(v___x_55_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
else
{
v___y_39_ = v___x_37_;
goto v___jp_38_;
}
}
}
else
{
lean_object* v___x_58_; lean_object* v___x_59_; 
lean_del_object(v___x_35_);
lean_dec(v_val_33_);
lean_dec_ref(v_env_30_);
lean_dec(v_declName_26_);
v___x_58_ = lean_box(v___x_31_);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
v___jp_38_:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = l_Lean_Compiler_mkUnsafeRecName(v_declName_26_);
v___x_41_ = l_Lean_Environment_find_x3f(v_env_30_, v___x_40_, v___x_37_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_42_ = lean_box(v___y_39_);
if (v_isShared_36_ == 0)
{
lean_ctor_set_tag(v___x_35_, 0);
lean_ctor_set(v___x_35_, 0, v___x_42_);
v___x_44_ = v___x_35_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_42_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
else
{
lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_53_; 
lean_del_object(v___x_35_);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_53_ == 0)
{
lean_object* v_unused_54_; 
v_unused_54_ = lean_ctor_get(v___x_41_, 0);
lean_dec(v_unused_54_);
v___x_47_ = v___x_41_;
v_isShared_48_ = v_isSharedCheck_53_;
goto v_resetjp_46_;
}
else
{
lean_dec(v___x_41_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_53_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; lean_object* v___x_51_; 
v___x_49_ = lean_box(v___x_37_);
if (v_isShared_48_ == 0)
{
lean_ctor_set_tag(v___x_47_, 0);
lean_ctor_set(v___x_47_, 0, v___x_49_);
v___x_51_ = v___x_47_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_49_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
}
}
else
{
uint8_t v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
lean_dec(v___x_32_);
lean_dec_ref(v_env_30_);
lean_dec(v_declName_26_);
v___x_61_ = 1;
v___x_62_ = lean_box(v___x_61_);
v___x_63_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_63_, 0, v___x_62_);
return v___x_63_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg___boxed(lean_object* v_declName_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v_declName_64_, v_a_65_);
lean_dec(v_a_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe(lean_object* v_declName_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v_declName_68_, v_a_70_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_declIsNotUnsafe___boxed(lean_object* v_declName_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Compiler_LCNF_declIsNotUnsafe(v_declName_73_, v_a_74_, v_a_75_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
return v_res_77_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(lean_object* v_opts_78_, lean_object* v_opt_79_){
_start:
{
lean_object* v_name_80_; lean_object* v_defValue_81_; lean_object* v_map_82_; lean_object* v___x_83_; 
v_name_80_ = lean_ctor_get(v_opt_79_, 0);
v_defValue_81_ = lean_ctor_get(v_opt_79_, 1);
v_map_82_ = lean_ctor_get(v_opts_78_, 0);
v___x_83_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_82_, v_name_80_);
if (lean_obj_tag(v___x_83_) == 0)
{
uint8_t v___x_84_; 
v___x_84_ = lean_unbox(v_defValue_81_);
return v___x_84_;
}
else
{
lean_object* v_val_85_; 
v_val_85_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_val_85_);
lean_dec_ref_known(v___x_83_, 1);
if (lean_obj_tag(v_val_85_) == 1)
{
uint8_t v_v_86_; 
v_v_86_ = lean_ctor_get_uint8(v_val_85_, 0);
lean_dec_ref_known(v_val_85_, 0);
return v_v_86_;
}
else
{
uint8_t v___x_87_; 
lean_dec(v_val_85_);
v___x_87_ = lean_unbox(v_defValue_81_);
return v___x_87_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0___boxed(lean_object* v_opts_88_, lean_object* v_opt_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v_opts_88_, v_opt_89_);
lean_dec_ref(v_opt_89_);
lean_dec_ref(v_opts_88_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_92_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0);
v___x_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_95_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__1);
v___x_96_ = lean_unsigned_to_nat(0u);
v___x_97_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
lean_ctor_set(v___x_97_, 2, v___x_96_);
lean_ctor_set(v___x_97_, 3, v___x_96_);
lean_ctor_set(v___x_97_, 4, v___x_95_);
lean_ctor_set(v___x_97_, 5, v___x_95_);
lean_ctor_set(v___x_97_, 6, v___x_95_);
lean_ctor_set(v___x_97_, 7, v___x_95_);
lean_ctor_set(v___x_97_, 8, v___x_95_);
lean_ctor_set(v___x_97_, 9, v___x_95_);
lean_ctor_set(v___x_97_, 10, v___x_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(lean_object* v_msg_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_, lean_object* v___y_102_){
_start:
{
lean_object* v_ref_104_; lean_object* v___x_105_; lean_object* v_env_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_ref_104_ = lean_ctor_get(v___y_101_, 2);
v___x_105_ = lean_st_ref_get(v___y_102_);
v_env_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc_ref(v_env_106_);
lean_dec(v___x_105_);
v___x_107_ = lean_st_ref_get(v___y_100_);
v___x_108_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_99_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_131_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_131_ == 0)
{
v___x_111_ = v___x_108_;
v_isShared_112_ = v_isSharedCheck_131_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_131_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v_lctx_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_129_; 
v_lctx_113_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_129_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_129_ == 0)
{
lean_object* v_unused_130_; 
v_unused_130_ = lean_ctor_get(v___x_107_, 1);
lean_dec(v_unused_130_);
v___x_115_ = v___x_107_;
v_isShared_116_ = v_isSharedCheck_129_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_lctx_113_);
lean_dec(v___x_107_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_129_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_117_ = lean_unbox(v_a_109_);
lean_dec(v_a_109_);
v___x_118_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_113_, v___x_117_);
lean_dec_ref(v_lctx_113_);
v___x_119_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_101_);
v___x_120_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2);
v___x_121_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_121_, 0, v_env_106_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
lean_ctor_set(v___x_121_, 2, v___x_118_);
lean_ctor_set(v___x_121_, 3, v___x_119_);
if (v_isShared_116_ == 0)
{
lean_ctor_set_tag(v___x_115_, 3);
lean_ctor_set(v___x_115_, 1, v_msg_98_);
lean_ctor_set(v___x_115_, 0, v___x_121_);
v___x_123_ = v___x_115_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_121_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_msg_98_);
v___x_123_ = v_reuseFailAlloc_128_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
lean_object* v___x_124_; lean_object* v___x_126_; 
lean_inc(v_ref_104_);
v___x_124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_124_, 0, v_ref_104_);
lean_ctor_set(v___x_124_, 1, v___x_123_);
if (v_isShared_112_ == 0)
{
lean_ctor_set_tag(v___x_111_, 1);
lean_ctor_set(v___x_111_, 0, v___x_124_);
v___x_126_ = v___x_111_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_124_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
lean_dec(v___x_107_);
lean_dec_ref(v_env_106_);
lean_dec_ref(v_msg_98_);
v_a_132_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_108_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_108_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___boxed(lean_object* v_msg_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v_msg_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2(lean_object* v_00_u03b1_147_, lean_object* v_msg_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v_msg_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___boxed(lean_object* v_00_u03b1_155_, lean_object* v_msg_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2(v_00_u03b1_155_, v_msg_156_, v___y_157_, v___y_158_, v___y_159_, v___y_160_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
lean_dec(v___y_158_);
lean_dec_ref(v___y_157_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0(lean_object* v_k_163_, lean_object* v_b_164_, lean_object* v_c_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___x_171_; 
lean_inc(v___y_169_);
lean_inc_ref(v___y_168_);
lean_inc(v___y_167_);
lean_inc_ref(v___y_166_);
v___x_171_ = lean_apply_7(v_k_163_, v_b_164_, v_c_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_, lean_box(0));
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0___boxed(lean_object* v_k_172_, lean_object* v_b_173_, lean_object* v_c_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0(v_k_172_, v_b_173_, v_c_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(lean_object* v_e_181_, lean_object* v_k_182_, uint8_t v_cleanupAnnotations_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v___f_189_; uint8_t v___x_190_; uint8_t v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___f_189_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_189_, 0, v_k_182_);
v___x_190_ = 1;
v___x_191_ = 0;
v___x_192_ = lean_box(0);
v___x_193_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_181_, v___x_190_, v___x_191_, v___x_190_, v___x_191_, v___x_192_, v___f_189_, v_cleanupAnnotations_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
v_a_202_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_193_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_193_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___boxed(lean_object* v_e_210_, lean_object* v_k_211_, lean_object* v_cleanupAnnotations_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_218_; lean_object* v_res_219_; 
v_cleanupAnnotations_boxed_218_ = lean_unbox(v_cleanupAnnotations_212_);
v_res_219_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_e_210_, v_k_211_, v_cleanupAnnotations_boxed_218_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5(lean_object* v_00_u03b1_220_, lean_object* v_e_221_, lean_object* v_k_222_, uint8_t v_cleanupAnnotations_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_e_221_, v_k_222_, v_cleanupAnnotations_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___boxed(lean_object* v_00_u03b1_230_, lean_object* v_e_231_, lean_object* v_k_232_, lean_object* v_cleanupAnnotations_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_239_; lean_object* v_res_240_; 
v_cleanupAnnotations_boxed_239_ = lean_unbox(v_cleanupAnnotations_233_);
v_res_240_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5(v_00_u03b1_230_, v_e_231_, v_k_232_, v_cleanupAnnotations_boxed_239_, v___y_234_, v___y_235_, v___y_236_, v___y_237_);
lean_dec(v___y_237_);
lean_dec_ref(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(uint8_t v___x_241_, lean_object* v_a_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_snd_248_; 
v_snd_248_ = lean_ctor_get(v_a_242_, 1);
lean_inc(v_snd_248_);
if (lean_obj_tag(v_snd_248_) == 7)
{
lean_object* v_fst_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_276_; 
v_fst_249_ = lean_ctor_get(v_a_242_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v_a_242_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; 
v_unused_277_ = lean_ctor_get(v_a_242_, 1);
lean_dec(v_unused_277_);
v___x_251_ = v_a_242_;
v_isShared_252_ = v_isSharedCheck_276_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_fst_249_);
lean_dec(v_a_242_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_276_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v_binderName_253_; lean_object* v_binderType_254_; lean_object* v_body_255_; uint8_t v___y_257_; 
v_binderName_253_ = lean_ctor_get(v_snd_248_, 0);
lean_inc(v_binderName_253_);
v_binderType_254_ = lean_ctor_get(v_snd_248_, 1);
lean_inc_ref(v_binderType_254_);
v_body_255_ = lean_ctor_get(v_snd_248_, 2);
lean_inc_ref(v_body_255_);
lean_dec_ref_known(v_snd_248_, 3);
if (v___x_241_ == 0)
{
uint8_t v___x_274_; 
v___x_274_ = l_Lean_isMarkedBorrowed(v_binderType_254_);
v___y_257_ = v___x_274_;
goto v___jp_256_;
}
else
{
uint8_t v___x_275_; 
v___x_275_ = 0;
v___y_257_ = v___x_275_;
goto v___jp_256_;
}
v___jp_256_:
{
uint8_t v___x_258_; lean_object* v___x_259_; 
v___x_258_ = 0;
v___x_259_ = l_Lean_Compiler_LCNF_mkParam(v___x_258_, v_binderName_253_, v_binderType_254_, v___y_257_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
if (lean_obj_tag(v___x_259_) == 0)
{
lean_object* v_a_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
v_a_260_ = lean_ctor_get(v___x_259_, 0);
lean_inc(v_a_260_);
lean_dec_ref_known(v___x_259_, 1);
v___x_261_ = lean_array_push(v_fst_249_, v_a_260_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_body_255_);
lean_ctor_set(v___x_251_, 0, v___x_261_);
v___x_263_ = v___x_251_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_body_255_);
v___x_263_ = v_reuseFailAlloc_265_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
v_a_242_ = v___x_263_;
goto _start;
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_dec_ref(v_body_255_);
lean_del_object(v___x_251_);
lean_dec(v_fst_249_);
v_a_266_ = lean_ctor_get(v___x_259_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_259_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_259_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_259_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
}
}
else
{
lean_object* v_fst_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_286_; 
v_fst_278_ = lean_ctor_get(v_a_242_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v_a_242_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; 
v_unused_287_ = lean_ctor_get(v_a_242_, 1);
lean_dec(v_unused_287_);
v___x_280_ = v_a_242_;
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_fst_278_);
lean_dec(v_a_242_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_fst_278_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_snd_248_);
v___x_283_ = v_reuseFailAlloc_285_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; 
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg___boxed(lean_object* v___x_288_, lean_object* v_a_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
uint8_t v___x_13530__boxed_295_; lean_object* v_res_296_; 
v___x_13530__boxed_295_ = lean_unbox(v___x_288_);
v_res_296_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_13530__boxed_295_, v_a_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0(lean_object* v_expr_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_305_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0));
v___x_306_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_302_);
v___x_307_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
v___x_308_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v___x_306_, v___x_307_);
lean_dec_ref(v___x_306_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_305_);
lean_ctor_set(v___x_309_, 1, v_expr_299_);
v___x_310_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_308_, v___x_309_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
if (lean_obj_tag(v___x_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_319_; 
v_a_311_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_319_ == 0)
{
v___x_313_ = v___x_310_;
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_310_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_319_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v_fst_315_; lean_object* v___x_317_; 
v_fst_315_ = lean_ctor_get(v_a_311_, 0);
lean_inc(v_fst_315_);
lean_dec(v_a_311_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 0, v_fst_315_);
v___x_317_ = v___x_313_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_fst_315_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_327_; 
v_a_320_ = lean_ctor_get(v___x_310_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v___x_310_);
if (v_isSharedCheck_327_ == 0)
{
v___x_322_ = v___x_310_;
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_310_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_327_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v___x_325_; 
if (v_isShared_323_ == 0)
{
v___x_325_ = v___x_322_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_320_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
return v___x_325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___boxed(lean_object* v_expr_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_expr_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1(uint8_t v___x_335_, uint8_t v___x_336_, lean_object* v_xs_337_, lean_object* v_body_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_Meta_etaExpand(v_body_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; uint8_t v___x_346_; lean_object* v___x_347_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v___x_344_, 1);
v___x_346_ = 1;
v___x_347_ = l_Lean_Meta_mkLambdaFVars(v_xs_337_, v_a_345_, v___x_335_, v___x_336_, v___x_335_, v___x_336_, v___x_346_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
return v___x_347_;
}
else
{
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1___boxed(lean_object* v___x_348_, lean_object* v___x_349_, lean_object* v_xs_350_, lean_object* v_body_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
uint8_t v___x_13688__boxed_357_; uint8_t v___x_13689__boxed_358_; lean_object* v_res_359_; 
v___x_13688__boxed_357_ = lean_unbox(v___x_348_);
v___x_13689__boxed_358_ = lean_unbox(v___x_349_);
v_res_359_ = l_Lean_Compiler_LCNF_toDecl___lam__1(v___x_13688__boxed_357_, v___x_13689__boxed_358_, v_xs_350_, v_body_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
lean_dec_ref(v___y_352_);
lean_dec_ref(v_xs_350_);
return v_res_359_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(lean_object* v_as_360_, size_t v_i_361_, size_t v_stop_362_){
_start:
{
uint8_t v___x_363_; 
v___x_363_ = lean_usize_dec_eq(v_i_361_, v_stop_362_);
if (v___x_363_ == 0)
{
lean_object* v___x_364_; uint8_t v_borrow_365_; 
v___x_364_ = lean_array_uget_borrowed(v_as_360_, v_i_361_);
v_borrow_365_ = lean_ctor_get_uint8(v___x_364_, sizeof(void*)*3);
if (v_borrow_365_ == 0)
{
size_t v___x_366_; size_t v___x_367_; 
v___x_366_ = ((size_t)1ULL);
v___x_367_ = lean_usize_add(v_i_361_, v___x_366_);
v_i_361_ = v___x_367_;
goto _start;
}
else
{
return v_borrow_365_;
}
}
else
{
uint8_t v___x_369_; 
v___x_369_ = 0;
return v___x_369_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3___boxed(lean_object* v_as_370_, lean_object* v_i_371_, lean_object* v_stop_372_){
_start:
{
size_t v_i_boxed_373_; size_t v_stop_boxed_374_; uint8_t v_res_375_; lean_object* v_r_376_; 
v_i_boxed_373_ = lean_unbox_usize(v_i_371_);
lean_dec(v_i_371_);
v_stop_boxed_374_ = lean_unbox_usize(v_stop_372_);
lean_dec(v_stop_372_);
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_as_370_, v_i_boxed_373_, v_stop_boxed_374_);
lean_dec_ref(v_as_370_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(uint8_t v___x_377_, size_t v_sz_378_, size_t v_i_379_, lean_object* v_bs_380_, lean_object* v___y_381_){
_start:
{
uint8_t v___x_383_; 
v___x_383_ = lean_usize_dec_lt(v_i_379_, v_sz_378_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; 
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v_bs_380_);
return v___x_384_;
}
else
{
lean_object* v_v_385_; lean_object* v___x_386_; lean_object* v_bs_x27_387_; uint8_t v___x_388_; lean_object* v___x_389_; 
v_v_385_ = lean_array_uget(v_bs_380_, v_i_379_);
v___x_386_ = lean_unsigned_to_nat(0u);
v_bs_x27_387_ = lean_array_uset(v_bs_380_, v_i_379_, v___x_386_);
v___x_388_ = 0;
v___x_389_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v___x_388_, v_v_385_, v___x_377_, v___y_381_);
if (lean_obj_tag(v___x_389_) == 0)
{
lean_object* v_a_390_; size_t v___x_391_; size_t v___x_392_; lean_object* v___x_393_; 
v_a_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_a_390_);
lean_dec_ref_known(v___x_389_, 1);
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_add(v_i_379_, v___x_391_);
v___x_393_ = lean_array_uset(v_bs_x27_387_, v_i_379_, v_a_390_);
v_i_379_ = v___x_392_;
v_bs_380_ = v___x_393_;
goto _start;
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec_ref(v_bs_x27_387_);
v_a_395_ = lean_ctor_get(v___x_389_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_389_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_389_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_389_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___boxed(lean_object* v___x_403_, lean_object* v_sz_404_, lean_object* v_i_405_, lean_object* v_bs_406_, lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
uint8_t v___x_13730__boxed_409_; size_t v_sz_boxed_410_; size_t v_i_boxed_411_; lean_object* v_res_412_; 
v___x_13730__boxed_409_ = lean_unbox(v___x_403_);
v_sz_boxed_410_ = lean_unbox_usize(v_sz_404_);
lean_dec(v_sz_404_);
v_i_boxed_411_ = lean_unbox_usize(v_i_405_);
lean_dec(v_i_405_);
v_res_412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_13730__boxed_409_, v_sz_boxed_410_, v_i_boxed_411_, v_bs_406_, v___y_407_);
lean_dec(v___y_407_);
return v_res_412_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__1(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__0));
v___x_415_ = l_Lean_stringToMessageData(v___x_414_);
return v___x_415_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__3(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__2));
v___x_418_ = l_Lean_stringToMessageData(v___x_417_);
return v___x_418_;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_toDecl___closed__6(void){
_start:
{
lean_object* v___x_427_; uint64_t v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__5));
v___x_428_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__7(void){
_start:
{
uint64_t v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_429_ = lean_uint64_once(&l_Lean_Compiler_LCNF_toDecl___closed__6, &l_Lean_Compiler_LCNF_toDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__6);
v___x_430_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__5));
v___x_431_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set_uint64(v___x_431_, sizeof(void*)*1, v___x_429_);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__8(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__9(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_unsigned_to_nat(32u);
v___x_435_ = lean_mk_empty_array_with_capacity(v___x_434_);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__10(void){
_start:
{
size_t v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_437_ = ((size_t)5ULL);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_unsigned_to_nat(32u);
v___x_440_ = lean_mk_empty_array_with_capacity(v___x_439_);
v___x_441_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__9, &l_Lean_Compiler_LCNF_toDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__9);
v___x_442_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_440_);
lean_ctor_set(v___x_442_, 2, v___x_438_);
lean_ctor_set(v___x_442_, 3, v___x_438_);
lean_ctor_set_usize(v___x_442_, 4, v___x_437_);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__11(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_443_ = lean_box(1);
v___x_444_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_445_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v___x_444_);
lean_ctor_set(v___x_446_, 2, v___x_443_);
return v___x_446_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__13(void){
_start:
{
uint8_t v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_449_ = 1;
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_box(0);
v___x_452_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__12));
v___x_453_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__11, &l_Lean_Compiler_LCNF_toDecl___closed__11_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__11);
v___x_454_ = lean_box(1);
v___x_455_ = 0;
v___x_456_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_457_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_454_);
lean_ctor_set(v___x_457_, 2, v___x_453_);
lean_ctor_set(v___x_457_, 3, v___x_452_);
lean_ctor_set(v___x_457_, 4, v___x_451_);
lean_ctor_set(v___x_457_, 5, v___x_450_);
lean_ctor_set(v___x_457_, 6, v___x_451_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*7, v___x_455_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*7 + 1, v___x_455_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*7 + 2, v___x_455_);
lean_ctor_set_uint8(v___x_457_, sizeof(void*)*7 + 3, v___x_449_);
return v___x_457_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__14(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_459_ = lean_unsigned_to_nat(0u);
v___x_460_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_460_, 0, v___x_459_);
lean_ctor_set(v___x_460_, 1, v___x_459_);
lean_ctor_set(v___x_460_, 2, v___x_459_);
lean_ctor_set(v___x_460_, 3, v___x_459_);
lean_ctor_set(v___x_460_, 4, v___x_458_);
lean_ctor_set(v___x_460_, 5, v___x_458_);
lean_ctor_set(v___x_460_, 6, v___x_458_);
lean_ctor_set(v___x_460_, 7, v___x_458_);
lean_ctor_set(v___x_460_, 8, v___x_458_);
lean_ctor_set(v___x_460_, 9, v___x_458_);
lean_ctor_set(v___x_460_, 10, v___x_458_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__15(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_462_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
lean_ctor_set(v___x_462_, 2, v___x_461_);
lean_ctor_set(v___x_462_, 3, v___x_461_);
lean_ctor_set(v___x_462_, 4, v___x_461_);
lean_ctor_set(v___x_462_, 5, v___x_461_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__16(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
lean_ctor_set(v___x_464_, 2, v___x_463_);
lean_ctor_set(v___x_464_, 3, v___x_463_);
lean_ctor_set(v___x_464_, 4, v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__17(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_465_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__16, &l_Lean_Compiler_LCNF_toDecl___closed__16_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__16);
v___x_466_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_467_ = lean_box(1);
v___x_468_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__15, &l_Lean_Compiler_LCNF_toDecl___closed__15_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__15);
v___x_469_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__14, &l_Lean_Compiler_LCNF_toDecl___closed__14_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__14);
v___x_470_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_470_, 0, v___x_469_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
lean_ctor_set(v___x_470_, 2, v___x_467_);
lean_ctor_set(v___x_470_, 3, v___x_466_);
lean_ctor_set(v___x_470_, 4, v___x_465_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__19(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__18));
v___x_473_ = l_Lean_stringToMessageData(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__21(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__20));
v___x_476_ = l_Lean_stringToMessageData(v___x_475_);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__23(void){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__22));
v___x_479_ = l_Lean_stringToMessageData(v___x_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object* v_declName_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; uint8_t v___y_493_; lean_object* v___y_510_; lean_object* v___y_511_; uint8_t v___y_512_; lean_object* v_decl_513_; lean_object* v_name_514_; lean_object* v_params_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_529_; lean_object* v___y_530_; uint8_t v___y_531_; lean_object* v_decl_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_581_; uint8_t v___y_582_; lean_object* v___y_583_; lean_object* v___y_584_; lean_object* v___y_585_; lean_object* v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; uint8_t v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; uint8_t v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; uint8_t v___y_605_; lean_object* v_a_606_; uint8_t v___y_629_; lean_object* v___y_630_; uint8_t v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v_a_634_; lean_object* v___x_656_; lean_object* v___y_658_; lean_object* v___x_810_; 
v___x_656_ = lean_box(1);
v___x_810_ = l_Lean_Compiler_isUnsafeRecName_x3f(v_declName_480_);
if (lean_obj_tag(v___x_810_) == 1)
{
lean_object* v_val_811_; 
lean_dec(v_declName_480_);
v_val_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_val_811_);
lean_dec_ref_known(v___x_810_, 1);
v___y_658_ = v_val_811_;
goto v___jp_657_;
}
else
{
lean_dec(v___x_810_);
v___y_658_ = v_declName_480_;
goto v___jp_657_;
}
v___jp_486_:
{
if (v___y_493_ == 0)
{
lean_object* v___x_494_; 
lean_dec(v___y_489_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___y_487_);
return v___x_494_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
lean_dec_ref(v___y_487_);
v___x_495_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__1, &l_Lean_Compiler_LCNF_toDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__1);
v___x_496_ = l_Lean_MessageData_ofName(v___y_489_);
v___x_497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_495_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
v___x_498_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__3, &l_Lean_Compiler_LCNF_toDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__3);
v___x_499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v___x_499_, v___y_488_, v___y_491_, v___y_492_, v___y_490_);
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_508_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_a_501_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
v___jp_509_:
{
uint8_t v___x_520_; 
lean_inc(v_name_514_);
v___x_520_ = l_Lean_isExport(v___y_511_, v_name_514_);
if (v___x_520_ == 0)
{
lean_dec_ref(v_params_515_);
v___y_487_ = v_decl_513_;
v___y_488_ = v___y_516_;
v___y_489_ = v_name_514_;
v___y_490_ = v___y_519_;
v___y_491_ = v___y_517_;
v___y_492_ = v___y_518_;
v___y_493_ = v___y_512_;
goto v___jp_486_;
}
else
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_array_get_size(v_params_515_);
v___x_522_ = lean_nat_dec_lt(v___y_510_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
lean_dec_ref(v_params_515_);
lean_dec(v_name_514_);
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v_decl_513_);
return v___x_523_;
}
else
{
if (v___x_522_ == 0)
{
lean_object* v___x_524_; 
lean_dec_ref(v_params_515_);
lean_dec(v_name_514_);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v_decl_513_);
return v___x_524_;
}
else
{
size_t v___x_525_; size_t v___x_526_; uint8_t v___x_527_; 
v___x_525_ = ((size_t)0ULL);
v___x_526_ = lean_usize_of_nat(v___x_521_);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_params_515_, v___x_525_, v___x_526_);
lean_dec_ref(v_params_515_);
v___y_487_ = v_decl_513_;
v___y_488_ = v___y_516_;
v___y_489_ = v_name_514_;
v___y_490_ = v___y_519_;
v___y_491_ = v___y_517_;
v___y_492_ = v___y_518_;
v___y_493_ = v___x_527_;
goto v___jp_486_;
}
}
}
}
v___jp_528_:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_Compiler_LCNF_Decl_etaExpand(v_decl_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_object* v_a_538_; lean_object* v___x_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v_a_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_a_538_);
lean_dec_ref_known(v___x_537_, 1);
v___x_539_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_535_);
v___x_540_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
v___x_541_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v___x_539_, v___x_540_);
lean_dec_ref(v___x_539_);
if (v___x_541_ == 0)
{
lean_object* v_toSignature_542_; lean_object* v_name_543_; lean_object* v_params_544_; 
v_toSignature_542_ = lean_ctor_get(v_a_538_, 0);
v_name_543_ = lean_ctor_get(v_toSignature_542_, 0);
lean_inc(v_name_543_);
v_params_544_ = lean_ctor_get(v_toSignature_542_, 3);
lean_inc_ref(v_params_544_);
v___y_510_ = v___y_529_;
v___y_511_ = v___y_530_;
v___y_512_ = v___y_531_;
v_decl_513_ = v_a_538_;
v_name_514_ = v_name_543_;
v_params_515_ = v_params_544_;
v___y_516_ = v___y_533_;
v___y_517_ = v___y_534_;
v___y_518_ = v___y_535_;
v___y_519_ = v___y_536_;
goto v___jp_509_;
}
else
{
lean_object* v_toSignature_545_; lean_object* v_value_546_; uint8_t v_recursive_547_; lean_object* v_inlineAttr_x3f_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_579_; 
v_toSignature_545_ = lean_ctor_get(v_a_538_, 0);
v_value_546_ = lean_ctor_get(v_a_538_, 1);
v_recursive_547_ = lean_ctor_get_uint8(v_a_538_, sizeof(void*)*3);
v_inlineAttr_x3f_548_ = lean_ctor_get(v_a_538_, 2);
v_isSharedCheck_579_ = !lean_is_exclusive(v_a_538_);
if (v_isSharedCheck_579_ == 0)
{
v___x_550_ = v_a_538_;
v_isShared_551_ = v_isSharedCheck_579_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_inlineAttr_x3f_548_);
lean_inc(v_value_546_);
lean_inc(v_toSignature_545_);
lean_dec(v_a_538_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_579_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v_name_552_; lean_object* v_levelParams_553_; lean_object* v_type_554_; lean_object* v_params_555_; uint8_t v_safe_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_578_; 
v_name_552_ = lean_ctor_get(v_toSignature_545_, 0);
v_levelParams_553_ = lean_ctor_get(v_toSignature_545_, 1);
v_type_554_ = lean_ctor_get(v_toSignature_545_, 2);
v_params_555_ = lean_ctor_get(v_toSignature_545_, 3);
v_safe_556_ = lean_ctor_get_uint8(v_toSignature_545_, sizeof(void*)*4);
v_isSharedCheck_578_ = !lean_is_exclusive(v_toSignature_545_);
if (v_isSharedCheck_578_ == 0)
{
v___x_558_ = v_toSignature_545_;
v_isShared_559_ = v_isSharedCheck_578_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_params_555_);
lean_inc(v_type_554_);
lean_inc(v_levelParams_553_);
lean_inc(v_name_552_);
lean_dec(v_toSignature_545_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_578_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
size_t v_sz_560_; size_t v___x_561_; lean_object* v___x_562_; 
v_sz_560_ = lean_array_size(v_params_555_);
v___x_561_ = ((size_t)0ULL);
v___x_562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___y_531_, v_sz_560_, v___x_561_, v_params_555_, v___y_534_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc_n(v_a_563_, 2);
lean_dec_ref_known(v___x_562_, 1);
lean_inc(v_name_552_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 3, v_a_563_);
v___x_565_ = v___x_558_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_name_552_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_levelParams_553_);
lean_ctor_set(v_reuseFailAlloc_569_, 2, v_type_554_);
lean_ctor_set(v_reuseFailAlloc_569_, 3, v_a_563_);
lean_ctor_set_uint8(v_reuseFailAlloc_569_, sizeof(void*)*4, v_safe_556_);
v___x_565_ = v_reuseFailAlloc_569_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_567_; 
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 0, v___x_565_);
v___x_567_ = v___x_550_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v_value_546_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v_inlineAttr_x3f_548_);
lean_ctor_set_uint8(v_reuseFailAlloc_568_, sizeof(void*)*3, v_recursive_547_);
v___x_567_ = v_reuseFailAlloc_568_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
v___y_510_ = v___y_529_;
v___y_511_ = v___y_530_;
v___y_512_ = v___y_531_;
v_decl_513_ = v___x_567_;
v_name_514_ = v_name_552_;
v_params_515_ = v_a_563_;
v___y_516_ = v___y_533_;
v___y_517_ = v___y_534_;
v___y_518_ = v___y_535_;
v___y_519_ = v___y_536_;
goto v___jp_509_;
}
}
}
else
{
lean_object* v_a_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_577_; 
lean_del_object(v___x_558_);
lean_dec_ref(v_type_554_);
lean_dec(v_levelParams_553_);
lean_dec(v_name_552_);
lean_del_object(v___x_550_);
lean_dec(v_inlineAttr_x3f_548_);
lean_dec_ref(v_value_546_);
lean_dec_ref(v___y_530_);
v_a_570_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_577_ == 0)
{
v___x_572_ = v___x_562_;
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_a_570_);
lean_dec(v___x_562_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_577_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
lean_object* v___x_575_; 
if (v_isShared_573_ == 0)
{
v___x_575_ = v___x_572_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_530_);
return v___x_537_;
}
}
v___jp_580_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_594_ = l_Lean_ConstantInfo_levelParams(v___y_584_);
lean_dec_ref(v___y_584_);
v___x_595_ = lean_mk_empty_array_with_capacity(v___y_581_);
v___x_596_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_596_, 0, v___y_588_);
lean_ctor_set(v___x_596_, 1, v___x_594_);
lean_ctor_set(v___x_596_, 2, v___y_586_);
lean_ctor_set(v___x_596_, 3, v___x_595_);
lean_ctor_set_uint8(v___x_596_, sizeof(void*)*4, v___y_582_);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___y_585_);
v___x_598_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
lean_ctor_set(v___x_598_, 2, v___y_587_);
lean_ctor_set_uint8(v___x_598_, sizeof(void*)*3, v___y_589_);
v___y_529_ = v___y_581_;
v___y_530_ = v___y_583_;
v___y_531_ = v___y_589_;
v_decl_532_ = v___x_598_;
v___y_533_ = v___y_590_;
v___y_534_ = v___y_591_;
v___y_535_ = v___y_592_;
v___y_536_ = v___y_593_;
goto v___jp_528_;
}
v___jp_599_:
{
lean_object* v___x_607_; 
lean_inc_ref(v_a_606_);
v___x_607_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_a_606_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v_a_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_619_; 
v_a_608_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_619_ == 0)
{
v___x_610_ = v___x_607_;
v_isShared_611_ = v_isSharedCheck_619_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_a_608_);
lean_dec(v___x_607_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_619_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_617_; 
v___x_612_ = l_Lean_ConstantInfo_levelParams(v___y_601_);
lean_dec_ref(v___y_601_);
v___x_613_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_613_, 0, v___y_604_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
lean_ctor_set(v___x_613_, 2, v_a_606_);
lean_ctor_set(v___x_613_, 3, v_a_608_);
lean_ctor_set_uint8(v___x_613_, sizeof(void*)*4, v___y_600_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v___y_602_);
v___x_615_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
lean_ctor_set(v___x_615_, 2, v___y_603_);
lean_ctor_set_uint8(v___x_615_, sizeof(void*)*3, v___y_605_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_615_);
v___x_617_ = v___x_610_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v___x_615_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
else
{
lean_object* v_a_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
lean_dec_ref(v_a_606_);
lean_dec(v___y_604_);
lean_dec(v___y_603_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
v_a_620_ = lean_ctor_get(v___x_607_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_627_ == 0)
{
v___x_622_ = v___x_607_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_a_620_);
lean_dec(v___x_607_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_620_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
v___jp_628_:
{
lean_object* v___x_635_; 
lean_inc_ref(v_a_634_);
v___x_635_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_a_634_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_647_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_647_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_647_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_647_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_640_ = l_Lean_ConstantInfo_levelParams(v___y_630_);
lean_dec_ref(v___y_630_);
v___x_641_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_641_, 0, v___y_633_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
lean_ctor_set(v___x_641_, 2, v_a_634_);
lean_ctor_set(v___x_641_, 3, v_a_636_);
lean_ctor_set_uint8(v___x_641_, sizeof(void*)*4, v___y_629_);
v___x_642_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__4));
v___x_643_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
lean_ctor_set(v___x_643_, 2, v___y_632_);
lean_ctor_set_uint8(v___x_643_, sizeof(void*)*3, v___y_631_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v___x_643_);
v___x_645_ = v___x_638_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec_ref(v_a_634_);
lean_dec(v___y_633_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_630_);
v_a_648_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_635_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_635_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
v___jp_657_:
{
lean_object* v___x_659_; lean_object* v_a_660_; 
lean_inc(v___y_658_);
v___x_659_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v___y_658_, v_a_484_);
v_a_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc(v_a_660_);
lean_dec_ref(v___x_659_);
if (lean_obj_tag(v_a_660_) == 1)
{
lean_object* v_val_661_; lean_object* v___x_662_; lean_object* v_a_663_; lean_object* v___x_664_; lean_object* v_env_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v_val_661_ = lean_ctor_get(v_a_660_, 0);
lean_inc(v_val_661_);
lean_dec_ref_known(v_a_660_, 1);
lean_inc_n(v___y_658_, 3);
v___x_662_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v___y_658_, v_a_484_);
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref(v___x_662_);
v___x_664_ = lean_st_ref_get(v_a_484_);
v_env_665_ = lean_ctor_get(v___x_664_, 0);
lean_inc_ref_n(v_env_665_, 3);
lean_dec(v___x_664_);
v___x_666_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_665_, v___y_658_);
v___x_667_ = l_Lean_getExternAttrData_x3f(v_env_665_, v___y_658_);
if (lean_obj_tag(v___x_667_) == 1)
{
lean_object* v_val_668_; lean_object* v___x_669_; uint8_t v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
lean_dec_ref(v_env_665_);
v_val_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc(v_val_668_);
lean_dec_ref_known(v___x_667_, 1);
v___x_669_ = l_Lean_ConstantInfo_type(v_val_661_);
v___x_670_ = 0;
v___x_671_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__13, &l_Lean_Compiler_LCNF_toDecl___closed__13_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__13);
v___x_672_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__17, &l_Lean_Compiler_LCNF_toDecl___closed__17_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__17);
v___x_673_ = lean_st_mk_ref(v___x_672_);
v___x_674_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_669_, v___x_671_, v___x_673_, v_a_483_, v_a_484_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref_known(v___x_674_, 1);
v___x_676_ = lean_st_ref_get(v___x_673_);
lean_dec(v___x_673_);
lean_dec(v___x_676_);
v___x_677_ = lean_unbox(v_a_663_);
lean_dec(v_a_663_);
v___y_600_ = v___x_677_;
v___y_601_ = v_val_661_;
v___y_602_ = v_val_668_;
v___y_603_ = v___x_666_;
v___y_604_ = v___y_658_;
v___y_605_ = v___x_670_;
v_a_606_ = v_a_675_;
goto v___jp_599_;
}
else
{
lean_dec(v___x_673_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_678_; uint8_t v___x_679_; 
v_a_678_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_674_, 1);
v___x_679_ = lean_unbox(v_a_663_);
lean_dec(v_a_663_);
v___y_600_ = v___x_679_;
v___y_601_ = v_val_661_;
v___y_602_ = v_val_668_;
v___y_603_ = v___x_666_;
v___y_604_ = v___y_658_;
v___y_605_ = v___x_670_;
v_a_606_ = v_a_678_;
goto v___jp_599_;
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
lean_dec(v_val_668_);
lean_dec(v___x_666_);
lean_dec(v_a_663_);
lean_dec(v_val_661_);
lean_dec(v___y_658_);
v_a_680_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_674_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_674_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
else
{
uint8_t v___x_688_; uint8_t v___x_689_; 
lean_dec(v___x_667_);
lean_inc(v___y_658_);
lean_inc_ref(v_env_665_);
v___x_688_ = l_Lean_hasInitAttr(v_env_665_, v___y_658_);
v___x_689_ = 1;
if (v___x_688_ == 0)
{
lean_object* v___x_690_; 
lean_inc(v_val_661_);
v___x_690_ = l_Lean_ConstantInfo_value_x3f(v_val_661_, v___x_689_);
if (lean_obj_tag(v___x_690_) == 1)
{
lean_object* v_val_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___f_694_; lean_object* v___x_695_; uint8_t v___x_696_; uint8_t v___x_697_; uint8_t v___x_698_; lean_object* v___x_699_; uint64_t v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v_val_691_ = lean_ctor_get(v___x_690_, 0);
lean_inc(v_val_691_);
lean_dec_ref_known(v___x_690_, 1);
v___x_692_ = lean_box(v___x_688_);
v___x_693_ = lean_box(v___x_689_);
v___f_694_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lam__1___boxed), 9, 2);
lean_closure_set(v___f_694_, 0, v___x_692_);
lean_closure_set(v___f_694_, 1, v___x_693_);
v___x_695_ = l_Lean_ConstantInfo_type(v_val_661_);
v___x_696_ = 1;
v___x_697_ = 0;
v___x_698_ = 2;
v___x_699_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_699_, 0, v___x_688_);
lean_ctor_set_uint8(v___x_699_, 1, v___x_688_);
lean_ctor_set_uint8(v___x_699_, 2, v___x_688_);
lean_ctor_set_uint8(v___x_699_, 3, v___x_688_);
lean_ctor_set_uint8(v___x_699_, 4, v___x_688_);
lean_ctor_set_uint8(v___x_699_, 5, v___x_689_);
lean_ctor_set_uint8(v___x_699_, 6, v___x_689_);
lean_ctor_set_uint8(v___x_699_, 7, v___x_688_);
lean_ctor_set_uint8(v___x_699_, 8, v___x_689_);
lean_ctor_set_uint8(v___x_699_, 9, v___x_696_);
lean_ctor_set_uint8(v___x_699_, 10, v___x_697_);
lean_ctor_set_uint8(v___x_699_, 11, v___x_689_);
lean_ctor_set_uint8(v___x_699_, 12, v___x_689_);
lean_ctor_set_uint8(v___x_699_, 13, v___x_689_);
lean_ctor_set_uint8(v___x_699_, 14, v___x_698_);
lean_ctor_set_uint8(v___x_699_, 15, v___x_689_);
lean_ctor_set_uint8(v___x_699_, 16, v___x_689_);
lean_ctor_set_uint8(v___x_699_, 17, v___x_689_);
lean_ctor_set_uint8(v___x_699_, 18, v___x_689_);
lean_ctor_set_uint8(v___x_699_, 19, v___x_688_);
v___x_700_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_699_);
v___x_701_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_701_, 0, v___x_699_);
lean_ctor_set_uint64(v___x_701_, sizeof(void*)*1, v___x_700_);
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__11, &l_Lean_Compiler_LCNF_toDecl___closed__11_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__11);
v___x_704_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__12));
v___x_705_ = lean_box(0);
v___x_706_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_706_, 0, v___x_701_);
lean_ctor_set(v___x_706_, 1, v___x_656_);
lean_ctor_set(v___x_706_, 2, v___x_703_);
lean_ctor_set(v___x_706_, 3, v___x_704_);
lean_ctor_set(v___x_706_, 4, v___x_705_);
lean_ctor_set(v___x_706_, 5, v___x_702_);
lean_ctor_set(v___x_706_, 6, v___x_705_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*7, v___x_688_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*7 + 1, v___x_688_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*7 + 2, v___x_688_);
lean_ctor_set_uint8(v___x_706_, sizeof(void*)*7 + 3, v___x_689_);
v___x_707_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__17, &l_Lean_Compiler_LCNF_toDecl___closed__17_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__17);
v___x_708_ = lean_st_mk_ref(v___x_707_);
v___x_709_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_695_, v___x_706_, v___x_708_, v_a_483_, v_a_484_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___x_711_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v___x_711_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_val_691_, v___f_694_, v___x_688_, v___x_706_, v___x_708_, v_a_483_, v_a_484_);
lean_dec_ref_known(v___x_706_, 7);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref_known(v___x_711_, 1);
v___x_713_ = lean_st_ref_get(v___x_708_);
lean_dec(v___x_708_);
lean_dec(v___x_713_);
lean_inc(v_a_710_);
v___x_714_ = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(v_a_712_, v_a_710_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
if (lean_obj_tag(v_a_715_) == 1)
{
lean_object* v_k_716_; 
v_k_716_ = lean_ctor_get(v_a_715_, 1);
lean_inc_ref(v_k_716_);
if (lean_obj_tag(v_k_716_) == 5)
{
lean_object* v_decl_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_740_; 
v_decl_717_ = lean_ctor_get(v_a_715_, 0);
lean_inc_ref(v_decl_717_);
lean_dec_ref_known(v_a_715_, 2);
v_isSharedCheck_740_ = !lean_is_exclusive(v_k_716_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v_k_716_, 0);
lean_dec(v_unused_741_);
v___x_719_ = v_k_716_;
v_isShared_720_ = v_isSharedCheck_740_;
goto v_resetjp_718_;
}
else
{
lean_dec(v_k_716_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_740_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
uint8_t v___x_721_; lean_object* v___x_722_; 
v___x_721_ = 0;
v___x_722_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_721_, v_decl_717_, v___x_688_, v_a_482_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v_params_723_; lean_object* v_value_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; lean_object* v___x_729_; 
lean_dec_ref_known(v___x_722_, 1);
v_params_723_ = lean_ctor_get(v_decl_717_, 2);
lean_inc_ref(v_params_723_);
v_value_724_ = lean_ctor_get(v_decl_717_, 4);
lean_inc_ref(v_value_724_);
lean_dec_ref(v_decl_717_);
v___x_725_ = l_Lean_ConstantInfo_levelParams(v_val_661_);
lean_dec(v_val_661_);
v___x_726_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_726_, 0, v___y_658_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
lean_ctor_set(v___x_726_, 2, v_a_710_);
lean_ctor_set(v___x_726_, 3, v_params_723_);
v___x_727_ = lean_unbox(v_a_663_);
lean_dec(v_a_663_);
lean_ctor_set_uint8(v___x_726_, sizeof(void*)*4, v___x_727_);
if (v_isShared_720_ == 0)
{
lean_ctor_set_tag(v___x_719_, 0);
lean_ctor_set(v___x_719_, 0, v_value_724_);
v___x_729_ = v___x_719_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_value_724_);
v___x_729_ = v_reuseFailAlloc_731_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; 
v___x_730_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_730_, 0, v___x_726_);
lean_ctor_set(v___x_730_, 1, v___x_729_);
lean_ctor_set(v___x_730_, 2, v___x_666_);
lean_ctor_set_uint8(v___x_730_, sizeof(void*)*3, v___x_688_);
v___y_529_ = v___x_702_;
v___y_530_ = v_env_665_;
v___y_531_ = v___x_688_;
v_decl_532_ = v___x_730_;
v___y_533_ = v_a_481_;
v___y_534_ = v_a_482_;
v___y_535_ = v_a_483_;
v___y_536_ = v_a_484_;
goto v___jp_528_;
}
}
else
{
lean_object* v_a_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_739_; 
lean_del_object(v___x_719_);
lean_dec_ref(v_decl_717_);
lean_dec(v_a_710_);
lean_dec(v___x_666_);
lean_dec_ref(v_env_665_);
lean_dec(v_a_663_);
lean_dec(v_val_661_);
lean_dec(v___y_658_);
v_a_732_ = lean_ctor_get(v___x_722_, 0);
v_isSharedCheck_739_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_739_ == 0)
{
v___x_734_ = v___x_722_;
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_a_732_);
lean_dec(v___x_722_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_739_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v___x_737_; 
if (v_isShared_735_ == 0)
{
v___x_737_ = v___x_734_;
goto v_reusejp_736_;
}
else
{
lean_object* v_reuseFailAlloc_738_; 
v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
v___x_737_ = v_reuseFailAlloc_738_;
goto v_reusejp_736_;
}
v_reusejp_736_:
{
return v___x_737_;
}
}
}
}
}
else
{
uint8_t v___x_742_; 
lean_dec_ref(v_k_716_);
v___x_742_ = lean_unbox(v_a_663_);
lean_dec(v_a_663_);
v___y_581_ = v___x_702_;
v___y_582_ = v___x_742_;
v___y_583_ = v_env_665_;
v___y_584_ = v_val_661_;
v___y_585_ = v_a_715_;
v___y_586_ = v_a_710_;
v___y_587_ = v___x_666_;
v___y_588_ = v___y_658_;
v___y_589_ = v___x_688_;
v___y_590_ = v_a_481_;
v___y_591_ = v_a_482_;
v___y_592_ = v_a_483_;
v___y_593_ = v_a_484_;
goto v___jp_580_;
}
}
else
{
uint8_t v___x_743_; 
v___x_743_ = lean_unbox(v_a_663_);
lean_dec(v_a_663_);
v___y_581_ = v___x_702_;
v___y_582_ = v___x_743_;
v___y_583_ = v_env_665_;
v___y_584_ = v_val_661_;
v___y_585_ = v_a_715_;
v___y_586_ = v_a_710_;
v___y_587_ = v___x_666_;
v___y_588_ = v___y_658_;
v___y_589_ = v___x_688_;
v___y_590_ = v_a_481_;
v___y_591_ = v_a_482_;
v___y_592_ = v_a_483_;
v___y_593_ = v_a_484_;
goto v___jp_580_;
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_a_710_);
lean_dec(v___x_666_);
lean_dec_ref(v_env_665_);
lean_dec(v_a_663_);
lean_dec(v_val_661_);
lean_dec(v___y_658_);
v_a_744_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_714_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_714_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
else
{
lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_a_710_);
lean_dec(v___x_708_);
lean_dec(v___x_666_);
lean_dec_ref(v_env_665_);
lean_dec(v_a_663_);
lean_dec(v_val_661_);
lean_dec(v___y_658_);
v_a_752_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_711_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_711_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v___x_708_);
lean_dec_ref_known(v___x_706_, 7);
lean_dec_ref(v___f_694_);
lean_dec(v_val_691_);
lean_dec(v___x_666_);
lean_dec_ref(v_env_665_);
lean_dec(v_a_663_);
lean_dec(v_val_661_);
lean_dec(v___y_658_);
v_a_760_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_709_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_709_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec(v___x_690_);
lean_dec(v___x_666_);
lean_dec_ref(v_env_665_);
lean_dec(v_a_663_);
lean_dec(v_val_661_);
v___x_768_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__19, &l_Lean_Compiler_LCNF_toDecl___closed__19_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__19);
v___x_769_ = l_Lean_MessageData_ofConstName(v___y_658_, v___x_688_);
v___x_770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__21, &l_Lean_Compiler_LCNF_toDecl___closed__21_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__21);
v___x_772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
v___x_773_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v___x_772_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
return v___x_773_;
}
}
else
{
lean_object* v___x_774_; uint8_t v___x_775_; uint8_t v___x_776_; uint8_t v___x_777_; uint8_t v___x_778_; lean_object* v___x_779_; uint64_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
lean_dec_ref(v_env_665_);
v___x_774_ = l_Lean_ConstantInfo_type(v_val_661_);
v___x_775_ = 0;
v___x_776_ = 1;
v___x_777_ = 0;
v___x_778_ = 2;
v___x_779_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_779_, 0, v___x_775_);
lean_ctor_set_uint8(v___x_779_, 1, v___x_775_);
lean_ctor_set_uint8(v___x_779_, 2, v___x_775_);
lean_ctor_set_uint8(v___x_779_, 3, v___x_775_);
lean_ctor_set_uint8(v___x_779_, 4, v___x_775_);
lean_ctor_set_uint8(v___x_779_, 5, v___x_688_);
lean_ctor_set_uint8(v___x_779_, 6, v___x_688_);
lean_ctor_set_uint8(v___x_779_, 7, v___x_775_);
lean_ctor_set_uint8(v___x_779_, 8, v___x_688_);
lean_ctor_set_uint8(v___x_779_, 9, v___x_776_);
lean_ctor_set_uint8(v___x_779_, 10, v___x_777_);
lean_ctor_set_uint8(v___x_779_, 11, v___x_688_);
lean_ctor_set_uint8(v___x_779_, 12, v___x_688_);
lean_ctor_set_uint8(v___x_779_, 13, v___x_688_);
lean_ctor_set_uint8(v___x_779_, 14, v___x_778_);
lean_ctor_set_uint8(v___x_779_, 15, v___x_688_);
lean_ctor_set_uint8(v___x_779_, 16, v___x_688_);
lean_ctor_set_uint8(v___x_779_, 17, v___x_688_);
lean_ctor_set_uint8(v___x_779_, 18, v___x_688_);
lean_ctor_set_uint8(v___x_779_, 19, v___x_775_);
v___x_780_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_779_);
v___x_781_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_781_, 0, v___x_779_);
lean_ctor_set_uint64(v___x_781_, sizeof(void*)*1, v___x_780_);
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__11, &l_Lean_Compiler_LCNF_toDecl___closed__11_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__11);
v___x_784_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__12));
v___x_785_ = lean_box(0);
v___x_786_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_786_, 0, v___x_781_);
lean_ctor_set(v___x_786_, 1, v___x_656_);
lean_ctor_set(v___x_786_, 2, v___x_783_);
lean_ctor_set(v___x_786_, 3, v___x_784_);
lean_ctor_set(v___x_786_, 4, v___x_785_);
lean_ctor_set(v___x_786_, 5, v___x_782_);
lean_ctor_set(v___x_786_, 6, v___x_785_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*7, v___x_775_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*7 + 1, v___x_775_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*7 + 2, v___x_775_);
lean_ctor_set_uint8(v___x_786_, sizeof(void*)*7 + 3, v___x_689_);
v___x_787_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__17, &l_Lean_Compiler_LCNF_toDecl___closed__17_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__17);
v___x_788_ = lean_st_mk_ref(v___x_787_);
v___x_789_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_774_, v___x_786_, v___x_788_, v_a_483_, v_a_484_);
lean_dec_ref_known(v___x_786_, 7);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_791_; uint8_t v___x_792_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v___x_791_ = lean_st_ref_get(v___x_788_);
lean_dec(v___x_788_);
lean_dec(v___x_791_);
v___x_792_ = lean_unbox(v_a_663_);
lean_dec(v_a_663_);
v___y_629_ = v___x_792_;
v___y_630_ = v_val_661_;
v___y_631_ = v___x_775_;
v___y_632_ = v___x_666_;
v___y_633_ = v___y_658_;
v_a_634_ = v_a_790_;
goto v___jp_628_;
}
else
{
lean_dec(v___x_788_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_793_; uint8_t v___x_794_; 
v_a_793_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_789_, 1);
v___x_794_ = lean_unbox(v_a_663_);
lean_dec(v_a_663_);
v___y_629_ = v___x_794_;
v___y_630_ = v_val_661_;
v___y_631_ = v___x_775_;
v___y_632_ = v___x_666_;
v___y_633_ = v___y_658_;
v_a_634_ = v_a_793_;
goto v___jp_628_;
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec(v___x_666_);
lean_dec(v_a_663_);
lean_dec(v_val_661_);
lean_dec(v___y_658_);
v_a_795_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_789_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_789_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v_a_660_);
v___x_803_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__19, &l_Lean_Compiler_LCNF_toDecl___closed__19_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__19);
v___x_804_ = 0;
v___x_805_ = l_Lean_MessageData_ofConstName(v___y_658_, v___x_804_);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_803_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__23, &l_Lean_Compiler_LCNF_toDecl___closed__23_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__23);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v___x_808_, v_a_481_, v_a_482_, v_a_483_, v_a_484_);
return v___x_809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___boxed(lean_object* v_declName_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lean_Compiler_LCNF_toDecl(v_declName_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_);
lean_dec(v_a_816_);
lean_dec_ref(v_a_815_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(uint8_t v___x_819_, lean_object* v_inst_820_, lean_object* v_a_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_819_, v_a_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___boxed(lean_object* v___x_828_, lean_object* v_inst_829_, lean_object* v_a_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
uint8_t v___x_14781__boxed_836_; lean_object* v_res_837_; 
v___x_14781__boxed_836_ = lean_unbox(v___x_828_);
v_res_837_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(v___x_14781__boxed_836_, v_inst_829_, v_a_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4(uint8_t v___x_838_, size_t v_sz_839_, size_t v_i_840_, lean_object* v_bs_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_838_, v_sz_839_, v_i_840_, v_bs_841_, v___y_843_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___boxed(lean_object* v___x_848_, lean_object* v_sz_849_, lean_object* v_i_850_, lean_object* v_bs_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
uint8_t v___x_14804__boxed_857_; size_t v_sz_boxed_858_; size_t v_i_boxed_859_; lean_object* v_res_860_; 
v___x_14804__boxed_857_ = lean_unbox(v___x_848_);
v_sz_boxed_858_ = lean_unbox_usize(v_sz_849_);
lean_dec(v_sz_849_);
v_i_boxed_859_ = lean_unbox_usize(v_i_850_);
lean_dec(v_i_850_);
v_res_860_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4(v___x_14804__boxed_857_, v_sz_boxed_858_, v_i_boxed_859_, v_bs_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec_ref(v___y_852_);
return v_res_860_;
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
