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
lean_object* v_toCold_104_; lean_object* v_ref_105_; lean_object* v___x_106_; lean_object* v_env_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_toCold_104_ = lean_ctor_get(v___y_101_, 0);
v_ref_105_ = lean_ctor_get(v___y_101_, 2);
v___x_106_ = lean_st_ref_get(v___y_102_);
v_env_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc_ref(v_env_107_);
lean_dec(v___x_106_);
v___x_108_ = lean_st_ref_get(v___y_100_);
v___x_109_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_99_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_132_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_132_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_132_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_132_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_lctx_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_130_; 
v_lctx_114_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_130_ == 0)
{
lean_object* v_unused_131_; 
v_unused_131_ = lean_ctor_get(v___x_108_, 1);
lean_dec(v_unused_131_);
v___x_116_ = v___x_108_;
v_isShared_117_ = v_isSharedCheck_130_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_lctx_114_);
lean_dec(v___x_108_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_130_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v_options_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v_options_118_ = lean_ctor_get(v_toCold_104_, 2);
v___x_119_ = lean_unbox(v_a_110_);
lean_dec(v_a_110_);
v___x_120_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_114_, v___x_119_);
lean_dec_ref(v_lctx_114_);
v___x_121_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__2);
lean_inc_ref(v_options_118_);
v___x_122_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_122_, 0, v_env_107_);
lean_ctor_set(v___x_122_, 1, v___x_121_);
lean_ctor_set(v___x_122_, 2, v___x_120_);
lean_ctor_set(v___x_122_, 3, v_options_118_);
if (v_isShared_117_ == 0)
{
lean_ctor_set_tag(v___x_116_, 3);
lean_ctor_set(v___x_116_, 1, v_msg_98_);
lean_ctor_set(v___x_116_, 0, v___x_122_);
v___x_124_ = v___x_116_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v_msg_98_);
v___x_124_ = v_reuseFailAlloc_129_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
lean_object* v___x_125_; lean_object* v___x_127_; 
lean_inc(v_ref_105_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v_ref_105_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
if (v_isShared_113_ == 0)
{
lean_ctor_set_tag(v___x_112_, 1);
lean_ctor_set(v___x_112_, 0, v___x_125_);
v___x_127_ = v___x_112_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v___x_125_);
v___x_127_ = v_reuseFailAlloc_128_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
return v___x_127_;
}
}
}
}
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
lean_dec(v___x_108_);
lean_dec_ref(v_env_107_);
lean_dec_ref(v_msg_98_);
v_a_133_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___x_109_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_109_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_133_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___boxed(lean_object* v_msg_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v_msg_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
lean_dec(v___y_145_);
lean_dec_ref(v___y_144_);
lean_dec(v___y_143_);
lean_dec_ref(v___y_142_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2(lean_object* v_00_u03b1_148_, lean_object* v_msg_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v_msg_149_, v___y_150_, v___y_151_, v___y_152_, v___y_153_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___boxed(lean_object* v_00_u03b1_156_, lean_object* v_msg_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2(v_00_u03b1_156_, v_msg_157_, v___y_158_, v___y_159_, v___y_160_, v___y_161_);
lean_dec(v___y_161_);
lean_dec_ref(v___y_160_);
lean_dec(v___y_159_);
lean_dec_ref(v___y_158_);
return v_res_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0(lean_object* v_k_164_, lean_object* v_b_165_, lean_object* v_c_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v___x_172_; 
lean_inc(v___y_170_);
lean_inc_ref(v___y_169_);
lean_inc(v___y_168_);
lean_inc_ref(v___y_167_);
v___x_172_ = lean_apply_7(v_k_164_, v_b_165_, v_c_166_, v___y_167_, v___y_168_, v___y_169_, v___y_170_, lean_box(0));
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0___boxed(lean_object* v_k_173_, lean_object* v_b_174_, lean_object* v_c_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0(v_k_173_, v_b_174_, v_c_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
lean_dec(v___y_179_);
lean_dec_ref(v___y_178_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(lean_object* v_e_182_, lean_object* v_k_183_, uint8_t v_cleanupAnnotations_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v___f_190_; uint8_t v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___f_190_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_190_, 0, v_k_183_);
v___x_191_ = 1;
v___x_192_ = 0;
v___x_193_ = lean_box(0);
v___x_194_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_182_, v___x_191_, v___x_192_, v___x_191_, v___x_192_, v___x_193_, v___f_190_, v_cleanupAnnotations_184_, v___y_185_, v___y_186_, v___y_187_, v___y_188_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_202_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_202_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_202_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_200_; 
if (v_isShared_198_ == 0)
{
v___x_200_ = v___x_197_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_a_195_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
v_a_203_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_194_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_194_);
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
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg___boxed(lean_object* v_e_211_, lean_object* v_k_212_, lean_object* v_cleanupAnnotations_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_219_; lean_object* v_res_220_; 
v_cleanupAnnotations_boxed_219_ = lean_unbox(v_cleanupAnnotations_213_);
v_res_220_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_e_211_, v_k_212_, v_cleanupAnnotations_boxed_219_, v___y_214_, v___y_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5(lean_object* v_00_u03b1_221_, lean_object* v_e_222_, lean_object* v_k_223_, uint8_t v_cleanupAnnotations_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_e_222_, v_k_223_, v_cleanupAnnotations_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___boxed(lean_object* v_00_u03b1_231_, lean_object* v_e_232_, lean_object* v_k_233_, lean_object* v_cleanupAnnotations_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_240_; lean_object* v_res_241_; 
v_cleanupAnnotations_boxed_240_ = lean_unbox(v_cleanupAnnotations_234_);
v_res_241_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5(v_00_u03b1_231_, v_e_232_, v_k_233_, v_cleanupAnnotations_boxed_240_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(uint8_t v___x_242_, lean_object* v_a_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_snd_249_; 
v_snd_249_ = lean_ctor_get(v_a_243_, 1);
lean_inc(v_snd_249_);
if (lean_obj_tag(v_snd_249_) == 7)
{
lean_object* v_fst_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_277_; 
v_fst_250_ = lean_ctor_get(v_a_243_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v_a_243_);
if (v_isSharedCheck_277_ == 0)
{
lean_object* v_unused_278_; 
v_unused_278_ = lean_ctor_get(v_a_243_, 1);
lean_dec(v_unused_278_);
v___x_252_ = v_a_243_;
v_isShared_253_ = v_isSharedCheck_277_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_fst_250_);
lean_dec(v_a_243_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_277_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_binderName_254_; lean_object* v_binderType_255_; lean_object* v_body_256_; uint8_t v___y_258_; 
v_binderName_254_ = lean_ctor_get(v_snd_249_, 0);
lean_inc(v_binderName_254_);
v_binderType_255_ = lean_ctor_get(v_snd_249_, 1);
lean_inc_ref(v_binderType_255_);
v_body_256_ = lean_ctor_get(v_snd_249_, 2);
lean_inc_ref(v_body_256_);
lean_dec_ref_known(v_snd_249_, 3);
if (v___x_242_ == 0)
{
uint8_t v___x_275_; 
v___x_275_ = l_Lean_isMarkedBorrowed(v_binderType_255_);
v___y_258_ = v___x_275_;
goto v___jp_257_;
}
else
{
uint8_t v___x_276_; 
v___x_276_ = 0;
v___y_258_ = v___x_276_;
goto v___jp_257_;
}
v___jp_257_:
{
uint8_t v___x_259_; lean_object* v___x_260_; 
v___x_259_ = 0;
v___x_260_ = l_Lean_Compiler_LCNF_mkParam(v___x_259_, v_binderName_254_, v_binderType_255_, v___y_258_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_262_; lean_object* v___x_264_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_260_, 1);
v___x_262_ = lean_array_push(v_fst_250_, v_a_261_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v_body_256_);
lean_ctor_set(v___x_252_, 0, v___x_262_);
v___x_264_ = v___x_252_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_body_256_);
v___x_264_ = v_reuseFailAlloc_266_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
v_a_243_ = v___x_264_;
goto _start;
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec_ref(v_body_256_);
lean_del_object(v___x_252_);
lean_dec(v_fst_250_);
v_a_267_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_260_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_260_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
}
else
{
lean_object* v_fst_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_287_; 
v_fst_279_ = lean_ctor_get(v_a_243_, 0);
v_isSharedCheck_287_ = !lean_is_exclusive(v_a_243_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; 
v_unused_288_ = lean_ctor_get(v_a_243_, 1);
lean_dec(v_unused_288_);
v___x_281_ = v_a_243_;
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_fst_279_);
lean_dec(v_a_243_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_287_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_fst_279_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_snd_249_);
v___x_284_ = v_reuseFailAlloc_286_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
lean_object* v___x_285_; 
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg___boxed(lean_object* v___x_289_, lean_object* v_a_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
uint8_t v___x_13541__boxed_296_; lean_object* v_res_297_; 
v___x_13541__boxed_296_ = lean_unbox(v___x_289_);
v_res_297_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_13541__boxed_296_, v_a_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0(lean_object* v_expr_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_toCold_306_; lean_object* v_options_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_toCold_306_ = lean_ctor_get(v___y_303_, 0);
v_options_307_ = lean_ctor_get(v_toCold_306_, 2);
v___x_308_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___lam__0___closed__0));
v___x_309_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
v___x_310_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v_options_307_, v___x_309_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_308_);
lean_ctor_set(v___x_311_, 1, v_expr_300_);
v___x_312_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_310_, v___x_311_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_321_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_321_ == 0)
{
v___x_315_ = v___x_312_;
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v___x_312_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v_fst_317_; lean_object* v___x_319_; 
v_fst_317_ = lean_ctor_get(v_a_313_, 0);
lean_inc(v_fst_317_);
lean_dec(v_a_313_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v_fst_317_);
v___x_319_ = v___x_315_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_fst_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
else
{
lean_object* v_a_322_; lean_object* v___x_324_; uint8_t v_isShared_325_; uint8_t v_isSharedCheck_329_; 
v_a_322_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_329_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_329_ == 0)
{
v___x_324_ = v___x_312_;
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
else
{
lean_inc(v_a_322_);
lean_dec(v___x_312_);
v___x_324_ = lean_box(0);
v_isShared_325_ = v_isSharedCheck_329_;
goto v_resetjp_323_;
}
v_resetjp_323_:
{
lean_object* v___x_327_; 
if (v_isShared_325_ == 0)
{
v___x_327_ = v___x_324_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_a_322_);
v___x_327_ = v_reuseFailAlloc_328_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
return v___x_327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__0___boxed(lean_object* v_expr_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_expr_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1(uint8_t v___x_337_, uint8_t v___x_338_, lean_object* v_xs_339_, lean_object* v_body_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; 
v___x_346_ = l_Lean_Meta_etaExpand(v_body_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; uint8_t v___x_348_; lean_object* v___x_349_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref_known(v___x_346_, 1);
v___x_348_ = 1;
v___x_349_ = l_Lean_Meta_mkLambdaFVars(v_xs_339_, v_a_347_, v___x_337_, v___x_338_, v___x_337_, v___x_338_, v___x_348_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
return v___x_349_;
}
else
{
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___lam__1___boxed(lean_object* v___x_350_, lean_object* v___x_351_, lean_object* v_xs_352_, lean_object* v_body_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
uint8_t v___x_13697__boxed_359_; uint8_t v___x_13698__boxed_360_; lean_object* v_res_361_; 
v___x_13697__boxed_359_ = lean_unbox(v___x_350_);
v___x_13698__boxed_360_ = lean_unbox(v___x_351_);
v_res_361_ = l_Lean_Compiler_LCNF_toDecl___lam__1(v___x_13697__boxed_359_, v___x_13698__boxed_360_, v_xs_352_, v_body_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec_ref(v_xs_352_);
return v_res_361_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(lean_object* v_as_362_, size_t v_i_363_, size_t v_stop_364_){
_start:
{
uint8_t v___x_365_; 
v___x_365_ = lean_usize_dec_eq(v_i_363_, v_stop_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; uint8_t v_borrow_367_; 
v___x_366_ = lean_array_uget_borrowed(v_as_362_, v_i_363_);
v_borrow_367_ = lean_ctor_get_uint8(v___x_366_, sizeof(void*)*3);
if (v_borrow_367_ == 0)
{
size_t v___x_368_; size_t v___x_369_; 
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_add(v_i_363_, v___x_368_);
v_i_363_ = v___x_369_;
goto _start;
}
else
{
return v_borrow_367_;
}
}
else
{
uint8_t v___x_371_; 
v___x_371_ = 0;
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3___boxed(lean_object* v_as_372_, lean_object* v_i_373_, lean_object* v_stop_374_){
_start:
{
size_t v_i_boxed_375_; size_t v_stop_boxed_376_; uint8_t v_res_377_; lean_object* v_r_378_; 
v_i_boxed_375_ = lean_unbox_usize(v_i_373_);
lean_dec(v_i_373_);
v_stop_boxed_376_ = lean_unbox_usize(v_stop_374_);
lean_dec(v_stop_374_);
v_res_377_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_as_372_, v_i_boxed_375_, v_stop_boxed_376_);
lean_dec_ref(v_as_372_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(uint8_t v___x_379_, size_t v_sz_380_, size_t v_i_381_, lean_object* v_bs_382_, lean_object* v___y_383_){
_start:
{
uint8_t v___x_385_; 
v___x_385_ = lean_usize_dec_lt(v_i_381_, v_sz_380_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; 
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v_bs_382_);
return v___x_386_;
}
else
{
lean_object* v_v_387_; lean_object* v___x_388_; lean_object* v_bs_x27_389_; uint8_t v___x_390_; lean_object* v___x_391_; 
v_v_387_ = lean_array_uget(v_bs_382_, v_i_381_);
v___x_388_ = lean_unsigned_to_nat(0u);
v_bs_x27_389_ = lean_array_uset(v_bs_382_, v_i_381_, v___x_388_);
v___x_390_ = 0;
v___x_391_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamBorrowImp___redArg(v___x_390_, v_v_387_, v___x_379_, v___y_383_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; size_t v___x_393_; size_t v___x_394_; lean_object* v___x_395_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_391_, 1);
v___x_393_ = ((size_t)1ULL);
v___x_394_ = lean_usize_add(v_i_381_, v___x_393_);
v___x_395_ = lean_array_uset(v_bs_x27_389_, v_i_381_, v_a_392_);
v_i_381_ = v___x_394_;
v_bs_382_ = v___x_395_;
goto _start;
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec_ref(v_bs_x27_389_);
v_a_397_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_391_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_391_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg___boxed(lean_object* v___x_405_, lean_object* v_sz_406_, lean_object* v_i_407_, lean_object* v_bs_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
uint8_t v___x_13739__boxed_411_; size_t v_sz_boxed_412_; size_t v_i_boxed_413_; lean_object* v_res_414_; 
v___x_13739__boxed_411_ = lean_unbox(v___x_405_);
v_sz_boxed_412_ = lean_unbox_usize(v_sz_406_);
lean_dec(v_sz_406_);
v_i_boxed_413_ = lean_unbox_usize(v_i_407_);
lean_dec(v_i_407_);
v_res_414_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_13739__boxed_411_, v_sz_boxed_412_, v_i_boxed_413_, v_bs_408_, v___y_409_);
lean_dec(v___y_409_);
return v_res_414_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__1(void){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__0));
v___x_417_ = l_Lean_stringToMessageData(v___x_416_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__3(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__2));
v___x_420_ = l_Lean_stringToMessageData(v___x_419_);
return v___x_420_;
}
}
static uint64_t _init_l_Lean_Compiler_LCNF_toDecl___closed__6(void){
_start:
{
lean_object* v___x_429_; uint64_t v___x_430_; 
v___x_429_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__5));
v___x_430_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__7(void){
_start:
{
uint64_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = lean_uint64_once(&l_Lean_Compiler_LCNF_toDecl___closed__6, &l_Lean_Compiler_LCNF_toDecl___closed__6_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__6);
v___x_432_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__5));
v___x_433_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set_uint64(v___x_433_, sizeof(void*)*1, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__8(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_434_ = lean_obj_once(&l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0, &l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0_once, _init_l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg___closed__0);
v___x_435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__9(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_unsigned_to_nat(32u);
v___x_437_ = lean_mk_empty_array_with_capacity(v___x_436_);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__10(void){
_start:
{
size_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_439_ = ((size_t)5ULL);
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = lean_unsigned_to_nat(32u);
v___x_442_ = lean_mk_empty_array_with_capacity(v___x_441_);
v___x_443_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__9, &l_Lean_Compiler_LCNF_toDecl___closed__9_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__9);
v___x_444_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
lean_ctor_set(v___x_444_, 2, v___x_440_);
lean_ctor_set(v___x_444_, 3, v___x_440_);
lean_ctor_set_usize(v___x_444_, 4, v___x_439_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__11(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_445_ = lean_box(1);
v___x_446_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_447_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v___x_446_);
lean_ctor_set(v___x_448_, 2, v___x_445_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__13(void){
_start:
{
uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_451_ = 1;
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = lean_box(0);
v___x_454_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__12));
v___x_455_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__11, &l_Lean_Compiler_LCNF_toDecl___closed__11_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__11);
v___x_456_ = lean_box(1);
v___x_457_ = 0;
v___x_458_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__7, &l_Lean_Compiler_LCNF_toDecl___closed__7_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__7);
v___x_459_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_456_);
lean_ctor_set(v___x_459_, 2, v___x_455_);
lean_ctor_set(v___x_459_, 3, v___x_454_);
lean_ctor_set(v___x_459_, 4, v___x_453_);
lean_ctor_set(v___x_459_, 5, v___x_452_);
lean_ctor_set(v___x_459_, 6, v___x_453_);
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*7, v___x_457_);
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*7 + 1, v___x_457_);
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*7 + 2, v___x_457_);
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*7 + 3, v___x_451_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__14(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_461_ = lean_unsigned_to_nat(0u);
v___x_462_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_461_);
lean_ctor_set(v___x_462_, 2, v___x_461_);
lean_ctor_set(v___x_462_, 3, v___x_461_);
lean_ctor_set(v___x_462_, 4, v___x_460_);
lean_ctor_set(v___x_462_, 5, v___x_460_);
lean_ctor_set(v___x_462_, 6, v___x_460_);
lean_ctor_set(v___x_462_, 7, v___x_460_);
lean_ctor_set(v___x_462_, 8, v___x_460_);
lean_ctor_set(v___x_462_, 9, v___x_460_);
lean_ctor_set(v___x_462_, 10, v___x_460_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__15(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_464_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
lean_ctor_set(v___x_464_, 2, v___x_463_);
lean_ctor_set(v___x_464_, 3, v___x_463_);
lean_ctor_set(v___x_464_, 4, v___x_463_);
lean_ctor_set(v___x_464_, 5, v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__16(void){
_start:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__8, &l_Lean_Compiler_LCNF_toDecl___closed__8_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__8);
v___x_466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
lean_ctor_set(v___x_466_, 2, v___x_465_);
lean_ctor_set(v___x_466_, 3, v___x_465_);
lean_ctor_set(v___x_466_, 4, v___x_465_);
return v___x_466_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__17(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_467_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__16, &l_Lean_Compiler_LCNF_toDecl___closed__16_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__16);
v___x_468_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__10, &l_Lean_Compiler_LCNF_toDecl___closed__10_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__10);
v___x_469_ = lean_box(1);
v___x_470_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__15, &l_Lean_Compiler_LCNF_toDecl___closed__15_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__15);
v___x_471_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__14, &l_Lean_Compiler_LCNF_toDecl___closed__14_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__14);
v___x_472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
lean_ctor_set(v___x_472_, 2, v___x_469_);
lean_ctor_set(v___x_472_, 3, v___x_468_);
lean_ctor_set(v___x_472_, 4, v___x_467_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__19(void){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_474_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__18));
v___x_475_ = l_Lean_stringToMessageData(v___x_474_);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__21(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__20));
v___x_478_ = l_Lean_stringToMessageData(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_toDecl___closed__23(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__22));
v___x_481_ = l_Lean_stringToMessageData(v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl(lean_object* v_declName_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; uint8_t v___y_495_; uint8_t v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v_decl_515_; lean_object* v_name_516_; lean_object* v_params_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; uint8_t v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v_decl_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; uint8_t v___y_584_; lean_object* v___y_585_; uint8_t v___y_586_; lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v___y_603_; uint8_t v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; uint8_t v___y_608_; lean_object* v_a_609_; uint8_t v___y_632_; uint8_t v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v_a_637_; lean_object* v___x_659_; lean_object* v___y_661_; lean_object* v___x_813_; 
v___x_659_ = lean_box(1);
v___x_813_ = l_Lean_Compiler_isUnsafeRecName_x3f(v_declName_482_);
if (lean_obj_tag(v___x_813_) == 1)
{
lean_object* v_val_814_; 
lean_dec(v_declName_482_);
v_val_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_val_814_);
lean_dec_ref_known(v___x_813_, 1);
v___y_661_ = v_val_814_;
goto v___jp_660_;
}
else
{
lean_dec(v___x_813_);
v___y_661_ = v_declName_482_;
goto v___jp_660_;
}
v___jp_488_:
{
if (v___y_495_ == 0)
{
lean_object* v___x_496_; 
lean_dec(v___y_494_);
v___x_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_496_, 0, v___y_491_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_a_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_510_; 
lean_dec_ref(v___y_491_);
v___x_497_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__1, &l_Lean_Compiler_LCNF_toDecl___closed__1_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__1);
v___x_498_ = l_Lean_MessageData_ofName(v___y_494_);
v___x_499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_497_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v___x_500_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__3, &l_Lean_Compiler_LCNF_toDecl___closed__3_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__3);
v___x_501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v___x_501_, v___y_490_, v___y_492_, v___y_489_, v___y_493_);
v_a_503_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_510_ == 0)
{
v___x_505_ = v___x_502_;
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_a_503_);
lean_dec(v___x_502_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_510_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
v___jp_511_:
{
uint8_t v___x_522_; 
lean_inc(v_name_516_);
v___x_522_ = l_Lean_isExport(v___y_514_, v_name_516_);
if (v___x_522_ == 0)
{
lean_dec_ref(v_params_517_);
v___y_489_ = v___y_520_;
v___y_490_ = v___y_518_;
v___y_491_ = v_decl_515_;
v___y_492_ = v___y_519_;
v___y_493_ = v___y_521_;
v___y_494_ = v_name_516_;
v___y_495_ = v___y_512_;
goto v___jp_488_;
}
else
{
lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_523_ = lean_array_get_size(v_params_517_);
v___x_524_ = lean_nat_dec_lt(v___y_513_, v___x_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_dec_ref(v_params_517_);
lean_dec(v_name_516_);
v___x_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_525_, 0, v_decl_515_);
return v___x_525_;
}
else
{
if (v___x_524_ == 0)
{
lean_object* v___x_526_; 
lean_dec_ref(v_params_517_);
lean_dec(v_name_516_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v_decl_515_);
return v___x_526_;
}
else
{
size_t v___x_527_; size_t v___x_528_; uint8_t v___x_529_; 
v___x_527_ = ((size_t)0ULL);
v___x_528_ = lean_usize_of_nat(v___x_523_);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_toDecl_spec__3(v_params_517_, v___x_527_, v___x_528_);
lean_dec_ref(v_params_517_);
v___y_489_ = v___y_520_;
v___y_490_ = v___y_518_;
v___y_491_ = v_decl_515_;
v___y_492_ = v___y_519_;
v___y_493_ = v___y_521_;
v___y_494_ = v_name_516_;
v___y_495_ = v___x_529_;
goto v___jp_488_;
}
}
}
}
v___jp_530_:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Compiler_LCNF_Decl_etaExpand(v_decl_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_object* v_toCold_540_; lean_object* v_a_541_; lean_object* v_options_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v_toCold_540_ = lean_ctor_get(v___y_537_, 0);
v_a_541_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_a_541_);
lean_dec_ref_known(v___x_539_, 1);
v_options_542_ = lean_ctor_get(v_toCold_540_, 2);
v___x_543_ = l_Lean_Compiler_compiler_ignoreBorrowAnnotation;
v___x_544_ = l_Lean_Option_get___at___00Lean_Compiler_LCNF_toDecl_spec__0(v_options_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v_toSignature_545_; lean_object* v_name_546_; lean_object* v_params_547_; 
v_toSignature_545_ = lean_ctor_get(v_a_541_, 0);
v_name_546_ = lean_ctor_get(v_toSignature_545_, 0);
lean_inc(v_name_546_);
v_params_547_ = lean_ctor_get(v_toSignature_545_, 3);
lean_inc_ref(v_params_547_);
v___y_512_ = v___y_531_;
v___y_513_ = v___y_532_;
v___y_514_ = v___y_533_;
v_decl_515_ = v_a_541_;
v_name_516_ = v_name_546_;
v_params_517_ = v_params_547_;
v___y_518_ = v___y_535_;
v___y_519_ = v___y_536_;
v___y_520_ = v___y_537_;
v___y_521_ = v___y_538_;
goto v___jp_511_;
}
else
{
lean_object* v_toSignature_548_; lean_object* v_value_549_; uint8_t v_recursive_550_; lean_object* v_inlineAttr_x3f_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_582_; 
v_toSignature_548_ = lean_ctor_get(v_a_541_, 0);
v_value_549_ = lean_ctor_get(v_a_541_, 1);
v_recursive_550_ = lean_ctor_get_uint8(v_a_541_, sizeof(void*)*3);
v_inlineAttr_x3f_551_ = lean_ctor_get(v_a_541_, 2);
v_isSharedCheck_582_ = !lean_is_exclusive(v_a_541_);
if (v_isSharedCheck_582_ == 0)
{
v___x_553_ = v_a_541_;
v_isShared_554_ = v_isSharedCheck_582_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_inlineAttr_x3f_551_);
lean_inc(v_value_549_);
lean_inc(v_toSignature_548_);
lean_dec(v_a_541_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_582_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v_name_555_; lean_object* v_levelParams_556_; lean_object* v_type_557_; lean_object* v_params_558_; uint8_t v_safe_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_581_; 
v_name_555_ = lean_ctor_get(v_toSignature_548_, 0);
v_levelParams_556_ = lean_ctor_get(v_toSignature_548_, 1);
v_type_557_ = lean_ctor_get(v_toSignature_548_, 2);
v_params_558_ = lean_ctor_get(v_toSignature_548_, 3);
v_safe_559_ = lean_ctor_get_uint8(v_toSignature_548_, sizeof(void*)*4);
v_isSharedCheck_581_ = !lean_is_exclusive(v_toSignature_548_);
if (v_isSharedCheck_581_ == 0)
{
v___x_561_ = v_toSignature_548_;
v_isShared_562_ = v_isSharedCheck_581_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_params_558_);
lean_inc(v_type_557_);
lean_inc(v_levelParams_556_);
lean_inc(v_name_555_);
lean_dec(v_toSignature_548_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_581_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
size_t v_sz_563_; size_t v___x_564_; lean_object* v___x_565_; 
v_sz_563_ = lean_array_size(v_params_558_);
v___x_564_ = ((size_t)0ULL);
v___x_565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___y_531_, v_sz_563_, v___x_564_, v_params_558_, v___y_536_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_568_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc_n(v_a_566_, 2);
lean_dec_ref_known(v___x_565_, 1);
lean_inc(v_name_555_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 3, v_a_566_);
v___x_568_ = v___x_561_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_name_555_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_levelParams_556_);
lean_ctor_set(v_reuseFailAlloc_572_, 2, v_type_557_);
lean_ctor_set(v_reuseFailAlloc_572_, 3, v_a_566_);
lean_ctor_set_uint8(v_reuseFailAlloc_572_, sizeof(void*)*4, v_safe_559_);
v___x_568_ = v_reuseFailAlloc_572_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_570_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_568_);
v___x_570_ = v___x_553_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___x_568_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_value_549_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v_inlineAttr_x3f_551_);
lean_ctor_set_uint8(v_reuseFailAlloc_571_, sizeof(void*)*3, v_recursive_550_);
v___x_570_ = v_reuseFailAlloc_571_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
v___y_512_ = v___y_531_;
v___y_513_ = v___y_532_;
v___y_514_ = v___y_533_;
v_decl_515_ = v___x_570_;
v_name_516_ = v_name_555_;
v_params_517_ = v_a_566_;
v___y_518_ = v___y_535_;
v___y_519_ = v___y_536_;
v___y_520_ = v___y_537_;
v___y_521_ = v___y_538_;
goto v___jp_511_;
}
}
}
else
{
lean_object* v_a_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_580_; 
lean_del_object(v___x_561_);
lean_dec_ref(v_type_557_);
lean_dec(v_levelParams_556_);
lean_dec(v_name_555_);
lean_del_object(v___x_553_);
lean_dec(v_inlineAttr_x3f_551_);
lean_dec_ref(v_value_549_);
lean_dec_ref(v___y_533_);
v_a_573_ = lean_ctor_get(v___x_565_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_565_);
if (v_isSharedCheck_580_ == 0)
{
v___x_575_ = v___x_565_;
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_a_573_);
lean_dec(v___x_565_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_580_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_a_573_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___y_533_);
return v___x_539_;
}
}
v___jp_583_:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_597_ = l_Lean_ConstantInfo_levelParams(v___y_592_);
lean_dec_ref(v___y_592_);
v___x_598_ = lean_mk_empty_array_with_capacity(v___y_587_);
v___x_599_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_599_, 0, v___y_590_);
lean_ctor_set(v___x_599_, 1, v___x_597_);
lean_ctor_set(v___x_599_, 2, v___y_585_);
lean_ctor_set(v___x_599_, 3, v___x_598_);
lean_ctor_set_uint8(v___x_599_, sizeof(void*)*4, v___y_584_);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___y_589_);
v___x_601_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
lean_ctor_set(v___x_601_, 2, v___y_588_);
lean_ctor_set_uint8(v___x_601_, sizeof(void*)*3, v___y_586_);
v___y_531_ = v___y_586_;
v___y_532_ = v___y_587_;
v___y_533_ = v___y_591_;
v_decl_534_ = v___x_601_;
v___y_535_ = v___y_593_;
v___y_536_ = v___y_594_;
v___y_537_ = v___y_595_;
v___y_538_ = v___y_596_;
goto v___jp_530_;
}
v___jp_602_:
{
lean_object* v___x_610_; 
lean_inc_ref(v_a_609_);
v___x_610_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_a_609_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_622_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_622_ == 0)
{
v___x_613_ = v___x_610_;
v_isShared_614_ = v_isSharedCheck_622_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_610_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_622_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_615_ = l_Lean_ConstantInfo_levelParams(v___y_607_);
lean_dec_ref(v___y_607_);
v___x_616_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_616_, 0, v___y_606_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
lean_ctor_set(v___x_616_, 2, v_a_609_);
lean_ctor_set(v___x_616_, 3, v_a_611_);
lean_ctor_set_uint8(v___x_616_, sizeof(void*)*4, v___y_604_);
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v___y_603_);
v___x_618_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_618_, 0, v___x_616_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
lean_ctor_set(v___x_618_, 2, v___y_605_);
lean_ctor_set_uint8(v___x_618_, sizeof(void*)*3, v___y_608_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_618_);
v___x_620_ = v___x_613_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_630_; 
lean_dec_ref(v_a_609_);
lean_dec_ref(v___y_607_);
lean_dec(v___y_606_);
lean_dec(v___y_605_);
lean_dec(v___y_603_);
v_a_623_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_630_ == 0)
{
v___x_625_ = v___x_610_;
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_a_623_);
lean_dec(v___x_610_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_630_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_628_; 
if (v_isShared_626_ == 0)
{
v___x_628_ = v___x_625_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
v___jp_631_:
{
lean_object* v___x_638_; 
lean_inc_ref(v_a_637_);
v___x_638_ = l_Lean_Compiler_LCNF_toDecl___lam__0(v_a_637_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_650_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_650_ == 0)
{
v___x_641_ = v___x_638_;
v_isShared_642_ = v_isSharedCheck_650_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_a_639_);
lean_dec(v___x_638_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_650_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_643_ = l_Lean_ConstantInfo_levelParams(v___y_636_);
lean_dec_ref(v___y_636_);
v___x_644_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_644_, 0, v___y_635_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
lean_ctor_set(v___x_644_, 2, v_a_637_);
lean_ctor_set(v___x_644_, 3, v_a_639_);
lean_ctor_set_uint8(v___x_644_, sizeof(void*)*4, v___y_632_);
v___x_645_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__4));
v___x_646_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
lean_ctor_set(v___x_646_, 2, v___y_634_);
lean_ctor_set_uint8(v___x_646_, sizeof(void*)*3, v___y_633_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 0, v___x_646_);
v___x_648_ = v___x_641_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v_a_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
lean_dec(v___y_634_);
v_a_651_ = lean_ctor_get(v___x_638_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_638_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_638_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_638_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
v___jp_660_:
{
lean_object* v___x_662_; lean_object* v_a_663_; 
lean_inc(v___y_661_);
v___x_662_ = l_Lean_Compiler_LCNF_getDeclInfo_x3f___redArg(v___y_661_, v_a_486_);
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref(v___x_662_);
if (lean_obj_tag(v_a_663_) == 1)
{
lean_object* v_val_664_; lean_object* v___x_665_; lean_object* v_a_666_; lean_object* v___x_667_; lean_object* v_env_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v_val_664_ = lean_ctor_get(v_a_663_, 0);
lean_inc(v_val_664_);
lean_dec_ref_known(v_a_663_, 1);
lean_inc_n(v___y_661_, 3);
v___x_665_ = l_Lean_Compiler_LCNF_declIsNotUnsafe___redArg(v___y_661_, v_a_486_);
v_a_666_ = lean_ctor_get(v___x_665_, 0);
lean_inc(v_a_666_);
lean_dec_ref(v___x_665_);
v___x_667_ = lean_st_ref_get(v_a_486_);
v_env_668_ = lean_ctor_get(v___x_667_, 0);
lean_inc_ref_n(v_env_668_, 3);
lean_dec(v___x_667_);
v___x_669_ = l_Lean_Compiler_getInlineAttribute_x3f(v_env_668_, v___y_661_);
v___x_670_ = l_Lean_getExternAttrData_x3f(v_env_668_, v___y_661_);
if (lean_obj_tag(v___x_670_) == 1)
{
lean_object* v_val_671_; lean_object* v___x_672_; uint8_t v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec_ref(v_env_668_);
v_val_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_val_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_672_ = l_Lean_ConstantInfo_type(v_val_664_);
v___x_673_ = 0;
v___x_674_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__13, &l_Lean_Compiler_LCNF_toDecl___closed__13_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__13);
v___x_675_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__17, &l_Lean_Compiler_LCNF_toDecl___closed__17_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__17);
v___x_676_ = lean_st_mk_ref(v___x_675_);
v___x_677_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_672_, v___x_674_, v___x_676_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_677_, 1);
v___x_679_ = lean_st_ref_get(v___x_676_);
lean_dec(v___x_676_);
lean_dec(v___x_679_);
v___x_680_ = lean_unbox(v_a_666_);
lean_dec(v_a_666_);
v___y_603_ = v_val_671_;
v___y_604_ = v___x_680_;
v___y_605_ = v___x_669_;
v___y_606_ = v___y_661_;
v___y_607_ = v_val_664_;
v___y_608_ = v___x_673_;
v_a_609_ = v_a_678_;
goto v___jp_602_;
}
else
{
lean_dec(v___x_676_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_681_; uint8_t v___x_682_; 
v_a_681_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_681_);
lean_dec_ref_known(v___x_677_, 1);
v___x_682_ = lean_unbox(v_a_666_);
lean_dec(v_a_666_);
v___y_603_ = v_val_671_;
v___y_604_ = v___x_682_;
v___y_605_ = v___x_669_;
v___y_606_ = v___y_661_;
v___y_607_ = v_val_664_;
v___y_608_ = v___x_673_;
v_a_609_ = v_a_681_;
goto v___jp_602_;
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec(v_val_671_);
lean_dec(v___x_669_);
lean_dec(v_a_666_);
lean_dec(v_val_664_);
lean_dec(v___y_661_);
v_a_683_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_677_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_677_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
else
{
uint8_t v___x_691_; uint8_t v___x_692_; 
lean_dec(v___x_670_);
lean_inc(v___y_661_);
lean_inc_ref(v_env_668_);
v___x_691_ = l_Lean_hasInitAttr(v_env_668_, v___y_661_);
v___x_692_ = 1;
if (v___x_691_ == 0)
{
lean_object* v___x_693_; 
lean_inc(v_val_664_);
v___x_693_ = l_Lean_ConstantInfo_value_x3f(v_val_664_, v___x_692_);
if (lean_obj_tag(v___x_693_) == 1)
{
lean_object* v_val_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___f_697_; lean_object* v___x_698_; uint8_t v___x_699_; uint8_t v___x_700_; uint8_t v___x_701_; lean_object* v___x_702_; uint64_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_val_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_val_694_);
lean_dec_ref_known(v___x_693_, 1);
v___x_695_ = lean_box(v___x_691_);
v___x_696_ = lean_box(v___x_692_);
v___f_697_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_toDecl___lam__1___boxed), 9, 2);
lean_closure_set(v___f_697_, 0, v___x_695_);
lean_closure_set(v___f_697_, 1, v___x_696_);
v___x_698_ = l_Lean_ConstantInfo_type(v_val_664_);
v___x_699_ = 1;
v___x_700_ = 0;
v___x_701_ = 2;
v___x_702_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_702_, 0, v___x_691_);
lean_ctor_set_uint8(v___x_702_, 1, v___x_691_);
lean_ctor_set_uint8(v___x_702_, 2, v___x_691_);
lean_ctor_set_uint8(v___x_702_, 3, v___x_691_);
lean_ctor_set_uint8(v___x_702_, 4, v___x_691_);
lean_ctor_set_uint8(v___x_702_, 5, v___x_692_);
lean_ctor_set_uint8(v___x_702_, 6, v___x_692_);
lean_ctor_set_uint8(v___x_702_, 7, v___x_691_);
lean_ctor_set_uint8(v___x_702_, 8, v___x_692_);
lean_ctor_set_uint8(v___x_702_, 9, v___x_699_);
lean_ctor_set_uint8(v___x_702_, 10, v___x_700_);
lean_ctor_set_uint8(v___x_702_, 11, v___x_692_);
lean_ctor_set_uint8(v___x_702_, 12, v___x_692_);
lean_ctor_set_uint8(v___x_702_, 13, v___x_692_);
lean_ctor_set_uint8(v___x_702_, 14, v___x_701_);
lean_ctor_set_uint8(v___x_702_, 15, v___x_692_);
lean_ctor_set_uint8(v___x_702_, 16, v___x_692_);
lean_ctor_set_uint8(v___x_702_, 17, v___x_692_);
lean_ctor_set_uint8(v___x_702_, 18, v___x_692_);
lean_ctor_set_uint8(v___x_702_, 19, v___x_691_);
v___x_703_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_702_);
v___x_704_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_704_, 0, v___x_702_);
lean_ctor_set_uint64(v___x_704_, sizeof(void*)*1, v___x_703_);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__11, &l_Lean_Compiler_LCNF_toDecl___closed__11_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__11);
v___x_707_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__12));
v___x_708_ = lean_box(0);
v___x_709_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_709_, 0, v___x_704_);
lean_ctor_set(v___x_709_, 1, v___x_659_);
lean_ctor_set(v___x_709_, 2, v___x_706_);
lean_ctor_set(v___x_709_, 3, v___x_707_);
lean_ctor_set(v___x_709_, 4, v___x_708_);
lean_ctor_set(v___x_709_, 5, v___x_705_);
lean_ctor_set(v___x_709_, 6, v___x_708_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*7, v___x_691_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*7 + 1, v___x_691_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*7 + 2, v___x_691_);
lean_ctor_set_uint8(v___x_709_, sizeof(void*)*7 + 3, v___x_692_);
v___x_710_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__17, &l_Lean_Compiler_LCNF_toDecl___closed__17_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__17);
v___x_711_ = lean_st_mk_ref(v___x_710_);
v___x_712_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_698_, v___x_709_, v___x_711_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___x_714_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
v___x_714_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Compiler_LCNF_toDecl_spec__5___redArg(v_val_694_, v___f_697_, v___x_691_, v___x_709_, v___x_711_, v_a_485_, v_a_486_);
lean_dec_ref_known(v___x_709_, 7);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_a_715_);
lean_dec_ref_known(v___x_714_, 1);
v___x_716_ = lean_st_ref_get(v___x_711_);
lean_dec(v___x_711_);
lean_dec(v___x_716_);
lean_inc(v_a_713_);
v___x_717_ = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(v_a_715_, v_a_713_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_717_) == 0)
{
lean_object* v_a_718_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
lean_inc(v_a_718_);
lean_dec_ref_known(v___x_717_, 1);
if (lean_obj_tag(v_a_718_) == 1)
{
lean_object* v_k_719_; 
v_k_719_ = lean_ctor_get(v_a_718_, 1);
lean_inc_ref(v_k_719_);
if (lean_obj_tag(v_k_719_) == 5)
{
lean_object* v_decl_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_743_; 
v_decl_720_ = lean_ctor_get(v_a_718_, 0);
lean_inc_ref(v_decl_720_);
lean_dec_ref_known(v_a_718_, 2);
v_isSharedCheck_743_ = !lean_is_exclusive(v_k_719_);
if (v_isSharedCheck_743_ == 0)
{
lean_object* v_unused_744_; 
v_unused_744_ = lean_ctor_get(v_k_719_, 0);
lean_dec(v_unused_744_);
v___x_722_ = v_k_719_;
v_isShared_723_ = v_isSharedCheck_743_;
goto v_resetjp_721_;
}
else
{
lean_dec(v_k_719_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_743_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
uint8_t v___x_724_; lean_object* v___x_725_; 
v___x_724_ = 0;
v___x_725_ = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(v___x_724_, v_decl_720_, v___x_691_, v_a_484_);
if (lean_obj_tag(v___x_725_) == 0)
{
lean_object* v_params_726_; lean_object* v_value_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; lean_object* v___x_732_; 
lean_dec_ref_known(v___x_725_, 1);
v_params_726_ = lean_ctor_get(v_decl_720_, 2);
lean_inc_ref(v_params_726_);
v_value_727_ = lean_ctor_get(v_decl_720_, 4);
lean_inc_ref(v_value_727_);
lean_dec_ref(v_decl_720_);
v___x_728_ = l_Lean_ConstantInfo_levelParams(v_val_664_);
lean_dec(v_val_664_);
v___x_729_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_729_, 0, v___y_661_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
lean_ctor_set(v___x_729_, 2, v_a_713_);
lean_ctor_set(v___x_729_, 3, v_params_726_);
v___x_730_ = lean_unbox(v_a_666_);
lean_dec(v_a_666_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*4, v___x_730_);
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 0);
lean_ctor_set(v___x_722_, 0, v_value_727_);
v___x_732_ = v___x_722_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_value_727_);
v___x_732_ = v_reuseFailAlloc_734_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; 
v___x_733_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_733_, 0, v___x_729_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
lean_ctor_set(v___x_733_, 2, v___x_669_);
lean_ctor_set_uint8(v___x_733_, sizeof(void*)*3, v___x_691_);
v___y_531_ = v___x_691_;
v___y_532_ = v___x_705_;
v___y_533_ = v_env_668_;
v_decl_534_ = v___x_733_;
v___y_535_ = v_a_483_;
v___y_536_ = v_a_484_;
v___y_537_ = v_a_485_;
v___y_538_ = v_a_486_;
goto v___jp_530_;
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_del_object(v___x_722_);
lean_dec_ref(v_decl_720_);
lean_dec(v_a_713_);
lean_dec(v___x_669_);
lean_dec_ref(v_env_668_);
lean_dec(v_a_666_);
lean_dec(v_val_664_);
lean_dec(v___y_661_);
v_a_735_ = lean_ctor_get(v___x_725_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_725_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_725_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_725_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
else
{
uint8_t v___x_745_; 
lean_dec_ref(v_k_719_);
v___x_745_ = lean_unbox(v_a_666_);
lean_dec(v_a_666_);
v___y_584_ = v___x_745_;
v___y_585_ = v_a_713_;
v___y_586_ = v___x_691_;
v___y_587_ = v___x_705_;
v___y_588_ = v___x_669_;
v___y_589_ = v_a_718_;
v___y_590_ = v___y_661_;
v___y_591_ = v_env_668_;
v___y_592_ = v_val_664_;
v___y_593_ = v_a_483_;
v___y_594_ = v_a_484_;
v___y_595_ = v_a_485_;
v___y_596_ = v_a_486_;
goto v___jp_583_;
}
}
else
{
uint8_t v___x_746_; 
v___x_746_ = lean_unbox(v_a_666_);
lean_dec(v_a_666_);
v___y_584_ = v___x_746_;
v___y_585_ = v_a_713_;
v___y_586_ = v___x_691_;
v___y_587_ = v___x_705_;
v___y_588_ = v___x_669_;
v___y_589_ = v_a_718_;
v___y_590_ = v___y_661_;
v___y_591_ = v_env_668_;
v___y_592_ = v_val_664_;
v___y_593_ = v_a_483_;
v___y_594_ = v_a_484_;
v___y_595_ = v_a_485_;
v___y_596_ = v_a_486_;
goto v___jp_583_;
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v_a_713_);
lean_dec(v___x_669_);
lean_dec_ref(v_env_668_);
lean_dec(v_a_666_);
lean_dec(v_val_664_);
lean_dec(v___y_661_);
v_a_747_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_717_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_717_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v_a_713_);
lean_dec(v___x_711_);
lean_dec(v___x_669_);
lean_dec_ref(v_env_668_);
lean_dec(v_a_666_);
lean_dec(v_val_664_);
lean_dec(v___y_661_);
v_a_755_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_714_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_714_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec(v___x_711_);
lean_dec_ref_known(v___x_709_, 7);
lean_dec_ref(v___f_697_);
lean_dec(v_val_694_);
lean_dec(v___x_669_);
lean_dec_ref(v_env_668_);
lean_dec(v_a_666_);
lean_dec(v_val_664_);
lean_dec(v___y_661_);
v_a_763_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_712_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_712_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec(v___x_693_);
lean_dec(v___x_669_);
lean_dec_ref(v_env_668_);
lean_dec(v_a_666_);
lean_dec(v_val_664_);
v___x_771_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__19, &l_Lean_Compiler_LCNF_toDecl___closed__19_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__19);
v___x_772_ = l_Lean_MessageData_ofConstName(v___y_661_, v___x_691_);
v___x_773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__21, &l_Lean_Compiler_LCNF_toDecl___closed__21_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__21);
v___x_775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_773_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v___x_775_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_776_;
}
}
else
{
lean_object* v___x_777_; uint8_t v___x_778_; uint8_t v___x_779_; uint8_t v___x_780_; uint8_t v___x_781_; lean_object* v___x_782_; uint64_t v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
lean_dec_ref(v_env_668_);
v___x_777_ = l_Lean_ConstantInfo_type(v_val_664_);
v___x_778_ = 0;
v___x_779_ = 1;
v___x_780_ = 0;
v___x_781_ = 2;
v___x_782_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_782_, 0, v___x_778_);
lean_ctor_set_uint8(v___x_782_, 1, v___x_778_);
lean_ctor_set_uint8(v___x_782_, 2, v___x_778_);
lean_ctor_set_uint8(v___x_782_, 3, v___x_778_);
lean_ctor_set_uint8(v___x_782_, 4, v___x_778_);
lean_ctor_set_uint8(v___x_782_, 5, v___x_691_);
lean_ctor_set_uint8(v___x_782_, 6, v___x_691_);
lean_ctor_set_uint8(v___x_782_, 7, v___x_778_);
lean_ctor_set_uint8(v___x_782_, 8, v___x_691_);
lean_ctor_set_uint8(v___x_782_, 9, v___x_779_);
lean_ctor_set_uint8(v___x_782_, 10, v___x_780_);
lean_ctor_set_uint8(v___x_782_, 11, v___x_691_);
lean_ctor_set_uint8(v___x_782_, 12, v___x_691_);
lean_ctor_set_uint8(v___x_782_, 13, v___x_691_);
lean_ctor_set_uint8(v___x_782_, 14, v___x_781_);
lean_ctor_set_uint8(v___x_782_, 15, v___x_691_);
lean_ctor_set_uint8(v___x_782_, 16, v___x_691_);
lean_ctor_set_uint8(v___x_782_, 17, v___x_691_);
lean_ctor_set_uint8(v___x_782_, 18, v___x_691_);
lean_ctor_set_uint8(v___x_782_, 19, v___x_778_);
v___x_783_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_782_);
v___x_784_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_784_, 0, v___x_782_);
lean_ctor_set_uint64(v___x_784_, sizeof(void*)*1, v___x_783_);
v___x_785_ = lean_unsigned_to_nat(0u);
v___x_786_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__11, &l_Lean_Compiler_LCNF_toDecl___closed__11_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__11);
v___x_787_ = ((lean_object*)(l_Lean_Compiler_LCNF_toDecl___closed__12));
v___x_788_ = lean_box(0);
v___x_789_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_789_, 0, v___x_784_);
lean_ctor_set(v___x_789_, 1, v___x_659_);
lean_ctor_set(v___x_789_, 2, v___x_786_);
lean_ctor_set(v___x_789_, 3, v___x_787_);
lean_ctor_set(v___x_789_, 4, v___x_788_);
lean_ctor_set(v___x_789_, 5, v___x_785_);
lean_ctor_set(v___x_789_, 6, v___x_788_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*7, v___x_778_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*7 + 1, v___x_778_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*7 + 2, v___x_778_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*7 + 3, v___x_692_);
v___x_790_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__17, &l_Lean_Compiler_LCNF_toDecl___closed__17_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__17);
v___x_791_ = lean_st_mk_ref(v___x_790_);
v___x_792_ = l_Lean_Compiler_LCNF_toLCNFType(v___x_777_, v___x_789_, v___x_791_, v_a_485_, v_a_486_);
lean_dec_ref_known(v___x_789_, 7);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v___x_794_ = lean_st_ref_get(v___x_791_);
lean_dec(v___x_791_);
lean_dec(v___x_794_);
v___x_795_ = lean_unbox(v_a_666_);
lean_dec(v_a_666_);
v___y_632_ = v___x_795_;
v___y_633_ = v___x_778_;
v___y_634_ = v___x_669_;
v___y_635_ = v___y_661_;
v___y_636_ = v_val_664_;
v_a_637_ = v_a_793_;
goto v___jp_631_;
}
else
{
lean_dec(v___x_791_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_796_; uint8_t v___x_797_; 
v_a_796_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_792_, 1);
v___x_797_ = lean_unbox(v_a_666_);
lean_dec(v_a_666_);
v___y_632_ = v___x_797_;
v___y_633_ = v___x_778_;
v___y_634_ = v___x_669_;
v___y_635_ = v___y_661_;
v___y_636_ = v_val_664_;
v_a_637_ = v_a_796_;
goto v___jp_631_;
}
else
{
lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v___x_669_);
lean_dec(v_a_666_);
lean_dec(v_val_664_);
lean_dec(v___y_661_);
v_a_798_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_792_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_792_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_806_; uint8_t v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
lean_dec(v_a_663_);
v___x_806_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__19, &l_Lean_Compiler_LCNF_toDecl___closed__19_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__19);
v___x_807_ = 0;
v___x_808_ = l_Lean_MessageData_ofConstName(v___y_661_, v___x_807_);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_806_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = lean_obj_once(&l_Lean_Compiler_LCNF_toDecl___closed__23, &l_Lean_Compiler_LCNF_toDecl___closed__23_once, _init_l_Lean_Compiler_LCNF_toDecl___closed__23);
v___x_811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_809_);
lean_ctor_set(v___x_811_, 1, v___x_810_);
v___x_812_ = l_Lean_throwError___at___00Lean_Compiler_LCNF_toDecl_spec__2___redArg(v___x_811_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_toDecl___boxed(lean_object* v_declName_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Compiler_LCNF_toDecl(v_declName_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
lean_dec_ref(v_a_816_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(uint8_t v___x_822_, lean_object* v_inst_823_, lean_object* v_a_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___redArg(v___x_822_, v_a_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1___boxed(lean_object* v___x_831_, lean_object* v_inst_832_, lean_object* v_a_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
uint8_t v___x_14788__boxed_839_; lean_object* v_res_840_; 
v___x_14788__boxed_839_ = lean_unbox(v___x_831_);
v_res_840_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Compiler_LCNF_toDecl_spec__1(v___x_14788__boxed_839_, v_inst_832_, v_a_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4(uint8_t v___x_841_, size_t v_sz_842_, size_t v_i_843_, lean_object* v_bs_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___redArg(v___x_841_, v_sz_842_, v_i_843_, v_bs_844_, v___y_846_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4___boxed(lean_object* v___x_851_, lean_object* v_sz_852_, lean_object* v_i_853_, lean_object* v_bs_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
uint8_t v___x_14811__boxed_860_; size_t v_sz_boxed_861_; size_t v_i_boxed_862_; lean_object* v_res_863_; 
v___x_14811__boxed_860_ = lean_unbox(v___x_851_);
v_sz_boxed_861_ = lean_unbox_usize(v_sz_852_);
lean_dec(v_sz_852_);
v_i_boxed_862_ = lean_unbox_usize(v_i_853_);
lean_dec(v_i_853_);
v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_toDecl_spec__4(v___x_14811__boxed_860_, v_sz_boxed_861_, v_i_boxed_862_, v_bs_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
return v_res_863_;
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
