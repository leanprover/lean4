// Lean compiler output
// Module: Lean.Meta.RecExt
// Imports: public import Lean.Attributes
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "recExt"};
static const lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(7, 192, 118, 202, 43, 9, 55, 48)}};
static const lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_recExt;
static lean_once_cell_t l_Lean_Meta_markAsRecursive___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_markAsRecursive___redArg___closed__0;
static lean_once_cell_t l_Lean_Meta_markAsRecursive___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_markAsRecursive___redArg___closed__1;
static lean_once_cell_t l_Lean_Meta_markAsRecursive___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_markAsRecursive___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = ((lean_object*)(l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_));
v___x_8_ = ((lean_object*)(l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_));
v___x_9_ = l_Lean_mkTagDeclarationExtension(v___x_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2____boxed(lean_object* v_a_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_();
return v_res_11_;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___redArg___closed__0(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___redArg___closed__1(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_obj_once(&l_Lean_Meta_markAsRecursive___redArg___closed__0, &l_Lean_Meta_markAsRecursive___redArg___closed__0_once, _init_l_Lean_Meta_markAsRecursive___redArg___closed__0);
v___x_14_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___redArg___closed__2(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_obj_once(&l_Lean_Meta_markAsRecursive___redArg___closed__1, &l_Lean_Meta_markAsRecursive___redArg___closed__1_once, _init_l_Lean_Meta_markAsRecursive___redArg___closed__1);
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___redArg(lean_object* v_declName_17_, lean_object* v_a_18_){
_start:
{
lean_object* v___x_20_; lean_object* v_env_21_; lean_object* v_nextMacroScope_22_; lean_object* v_ngen_23_; lean_object* v_auxDeclNGen_24_; lean_object* v_traceState_25_; lean_object* v_messages_26_; lean_object* v_infoState_27_; lean_object* v_snapshotTasks_28_; lean_object* v_newDecls_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_42_; 
v___x_20_ = lean_st_ref_take(v_a_18_);
v_env_21_ = lean_ctor_get(v___x_20_, 0);
v_nextMacroScope_22_ = lean_ctor_get(v___x_20_, 1);
v_ngen_23_ = lean_ctor_get(v___x_20_, 2);
v_auxDeclNGen_24_ = lean_ctor_get(v___x_20_, 3);
v_traceState_25_ = lean_ctor_get(v___x_20_, 4);
v_messages_26_ = lean_ctor_get(v___x_20_, 6);
v_infoState_27_ = lean_ctor_get(v___x_20_, 7);
v_snapshotTasks_28_ = lean_ctor_get(v___x_20_, 8);
v_newDecls_29_ = lean_ctor_get(v___x_20_, 9);
v_isSharedCheck_42_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_42_ == 0)
{
lean_object* v_unused_43_; 
v_unused_43_ = lean_ctor_get(v___x_20_, 5);
lean_dec(v_unused_43_);
v___x_31_ = v___x_20_;
v_isShared_32_ = v_isSharedCheck_42_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_newDecls_29_);
lean_inc(v_snapshotTasks_28_);
lean_inc(v_infoState_27_);
lean_inc(v_messages_26_);
lean_inc(v_traceState_25_);
lean_inc(v_auxDeclNGen_24_);
lean_inc(v_ngen_23_);
lean_inc(v_nextMacroScope_22_);
lean_inc(v_env_21_);
lean_dec(v___x_20_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_42_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_37_; 
v___x_33_ = l_Lean_Meta_recExt;
v___x_34_ = l_Lean_TagDeclarationExtension_tag(v___x_33_, v_env_21_, v_declName_17_);
v___x_35_ = lean_obj_once(&l_Lean_Meta_markAsRecursive___redArg___closed__2, &l_Lean_Meta_markAsRecursive___redArg___closed__2_once, _init_l_Lean_Meta_markAsRecursive___redArg___closed__2);
if (v_isShared_32_ == 0)
{
lean_ctor_set(v___x_31_, 5, v___x_35_);
lean_ctor_set(v___x_31_, 0, v___x_34_);
v___x_37_ = v___x_31_;
goto v_reusejp_36_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_34_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v_nextMacroScope_22_);
lean_ctor_set(v_reuseFailAlloc_41_, 2, v_ngen_23_);
lean_ctor_set(v_reuseFailAlloc_41_, 3, v_auxDeclNGen_24_);
lean_ctor_set(v_reuseFailAlloc_41_, 4, v_traceState_25_);
lean_ctor_set(v_reuseFailAlloc_41_, 5, v___x_35_);
lean_ctor_set(v_reuseFailAlloc_41_, 6, v_messages_26_);
lean_ctor_set(v_reuseFailAlloc_41_, 7, v_infoState_27_);
lean_ctor_set(v_reuseFailAlloc_41_, 8, v_snapshotTasks_28_);
lean_ctor_set(v_reuseFailAlloc_41_, 9, v_newDecls_29_);
v___x_37_ = v_reuseFailAlloc_41_;
goto v_reusejp_36_;
}
v_reusejp_36_:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_st_ref_set(v_a_18_, v___x_37_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
return v___x_40_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___redArg___boxed(lean_object* v_declName_44_, lean_object* v_a_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_44_, v_a_45_);
lean_dec(v_a_45_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive(lean_object* v_declName_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_48_, v_a_50_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___boxed(lean_object* v_declName_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Meta_markAsRecursive(v_declName_53_, v_a_54_, v_a_55_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___redArg(lean_object* v_declName_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___x_61_; lean_object* v_env_62_; lean_object* v___x_63_; lean_object* v_toEnvExtension_64_; lean_object* v_asyncMode_65_; uint8_t v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_61_ = lean_st_ref_get(v_a_59_);
v_env_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc_ref(v_env_62_);
lean_dec(v___x_61_);
v___x_63_ = l_Lean_Meta_recExt;
v_toEnvExtension_64_ = lean_ctor_get(v___x_63_, 0);
v_asyncMode_65_ = lean_ctor_get(v_toEnvExtension_64_, 2);
v___x_66_ = l_Lean_TagDeclarationExtension_isTagged(v___x_63_, v_env_62_, v_declName_58_, v_asyncMode_65_);
v___x_67_ = lean_box(v___x_66_);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___redArg___boxed(lean_object* v_declName_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_69_, v_a_70_);
lean_dec(v_a_70_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition(lean_object* v_declName_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_73_, v_a_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___boxed(lean_object* v_declName_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Meta_isRecursiveDefinition(v_declName_78_, v_a_79_, v_a_80_);
lean_dec(v_a_80_);
lean_dec_ref(v_a_79_);
return v_res_82_;
}
}
lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_RecExt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_recExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_recExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_RecExt(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Attributes(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_RecExt(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_RecExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_RecExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_RecExt(builtin);
}
#ifdef __cplusplus
}
#endif
