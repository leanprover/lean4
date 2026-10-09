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
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; 
v___x_7_ = ((lean_object*)(l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_));
v___x_8_ = ((lean_object*)(l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_));
v___x_9_ = 0;
v___x_10_ = l_Lean_mkTagDeclarationExtension(v___x_7_, v___x_8_, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_11_;
v_res_11_ = l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_();
stack->m_obj
 = v_res_11_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2____boxed(lean_object* v_a_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_();
return v_res_13_;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___redArg___closed__0(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___redArg___closed__1(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_obj_once(&l_Lean_Meta_markAsRecursive___redArg___closed__0, &l_Lean_Meta_markAsRecursive___redArg___closed__0_once, _init_l_Lean_Meta_markAsRecursive___redArg___closed__0);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_Meta_markAsRecursive___redArg___closed__2(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_obj_once(&l_Lean_Meta_markAsRecursive___redArg___closed__1, &l_Lean_Meta_markAsRecursive___redArg___closed__1_once, _init_l_Lean_Meta_markAsRecursive___redArg___closed__1);
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
lean_ctor_set(v___x_18_, 1, v___x_17_);
return v___x_18_;
}
}
lean_object* l_Lean_Meta_markAsRecursive___redArg(lean_object* v_declName_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_22_; lean_object* v_env_23_; lean_object* v_nextMacroScope_24_; lean_object* v_ngen_25_; lean_object* v_auxDeclNGen_26_; lean_object* v_traceState_27_; lean_object* v_recordedDeps_28_; lean_object* v_messages_29_; lean_object* v_infoState_30_; lean_object* v_snapshotTasks_31_; lean_object* v___x_33_; uint8_t v_isShared_34_; uint8_t v_isSharedCheck_44_; 
v___x_22_ = lean_st_ref_take(v_a_20_);
v_env_23_ = lean_ctor_get(v___x_22_, 0);
v_nextMacroScope_24_ = lean_ctor_get(v___x_22_, 1);
v_ngen_25_ = lean_ctor_get(v___x_22_, 2);
v_auxDeclNGen_26_ = lean_ctor_get(v___x_22_, 3);
v_traceState_27_ = lean_ctor_get(v___x_22_, 4);
v_recordedDeps_28_ = lean_ctor_get(v___x_22_, 6);
v_messages_29_ = lean_ctor_get(v___x_22_, 7);
v_infoState_30_ = lean_ctor_get(v___x_22_, 8);
v_snapshotTasks_31_ = lean_ctor_get(v___x_22_, 9);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_44_ == 0)
{
lean_object* v_unused_45_; 
v_unused_45_ = lean_ctor_get(v___x_22_, 5);
lean_dec(v_unused_45_);
v___x_33_ = v___x_22_;
v_isShared_34_ = v_isSharedCheck_44_;
goto v_resetjp_32_;
}
else
{
lean_inc(v_snapshotTasks_31_);
lean_inc(v_infoState_30_);
lean_inc(v_messages_29_);
lean_inc(v_recordedDeps_28_);
lean_inc(v_traceState_27_);
lean_inc(v_auxDeclNGen_26_);
lean_inc(v_ngen_25_);
lean_inc(v_nextMacroScope_24_);
lean_inc(v_env_23_);
lean_dec(v___x_22_);
v___x_33_ = lean_box(0);
v_isShared_34_ = v_isSharedCheck_44_;
goto v_resetjp_32_;
}
v_resetjp_32_:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_35_ = lean_box(0);
v___x_36_ = l_Lean_Meta_recExt;
v___x_37_ = l_Lean_TagDeclarationExtension_tag(v___x_36_, v_env_23_, v_declName_19_);
v___x_38_ = lean_obj_once(&l_Lean_Meta_markAsRecursive___redArg___closed__2, &l_Lean_Meta_markAsRecursive___redArg___closed__2_once, _init_l_Lean_Meta_markAsRecursive___redArg___closed__2);
if (v_isShared_34_ == 0)
{
lean_ctor_set(v___x_33_, 5, v___x_38_);
lean_ctor_set(v___x_33_, 0, v___x_37_);
v___x_40_ = v___x_33_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_43_, 1, v_nextMacroScope_24_);
lean_ctor_set(v_reuseFailAlloc_43_, 2, v_ngen_25_);
lean_ctor_set(v_reuseFailAlloc_43_, 3, v_auxDeclNGen_26_);
lean_ctor_set(v_reuseFailAlloc_43_, 4, v_traceState_27_);
lean_ctor_set(v_reuseFailAlloc_43_, 5, v___x_38_);
lean_ctor_set(v_reuseFailAlloc_43_, 6, v_recordedDeps_28_);
lean_ctor_set(v_reuseFailAlloc_43_, 7, v_messages_29_);
lean_ctor_set(v_reuseFailAlloc_43_, 8, v_infoState_30_);
lean_ctor_set(v_reuseFailAlloc_43_, 9, v_snapshotTasks_31_);
v___x_40_ = v_reuseFailAlloc_43_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_st_ref_put(v_a_20_, v___x_40_);
v___x_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_35_);
return v___x_42_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_markAsRecursive___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_19_ = stack[0].m_obj;
lean_object* v_a_20_ = stack[1].m_obj;
lean_object* v_res_46_;
v_res_46_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_19_, v_a_20_);
stack->m_obj
 = v_res_46_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___redArg___boxed(lean_object* v_declName_47_, lean_object* v_a_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_47_, v_a_48_);
lean_dec(v_a_48_);
return v_res_50_;
}
}
lean_object* l_Lean_Meta_markAsRecursive(lean_object* v_declName_51_, lean_object* v_a_52_, lean_object* v_a_53_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_51_, v_a_53_);
return v___x_55_;
}
}
LEAN_EXPORT void l_Lean_Meta_markAsRecursive_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_51_ = stack[0].m_obj;
lean_object* v_a_52_ = stack[1].m_obj;
lean_object* v_a_53_ = stack[2].m_obj;
lean_object* v_res_56_;
v_res_56_ = l_Lean_Meta_markAsRecursive(v_declName_51_, v_a_52_, v_a_53_);
stack->m_obj
 = v_res_56_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_markAsRecursive___boxed(lean_object* v_declName_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_Meta_markAsRecursive(v_declName_57_, v_a_58_, v_a_59_);
lean_dec(v_a_59_);
lean_dec_ref(v_a_58_);
return v_res_61_;
}
}
lean_object* l_Lean_Meta_isRecursiveDefinition___redArg(lean_object* v_declName_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_65_; lean_object* v_env_66_; lean_object* v___x_67_; lean_object* v_toEnvExtension_68_; lean_object* v_asyncMode_69_; uint8_t v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_65_ = lean_st_ref_get(v_a_63_);
v_env_66_ = lean_ctor_get(v___x_65_, 0);
lean_inc_ref(v_env_66_);
lean_dec(v___x_65_);
v___x_67_ = l_Lean_Meta_recExt;
v_toEnvExtension_68_ = lean_ctor_get(v___x_67_, 0);
v_asyncMode_69_ = lean_ctor_get(v_toEnvExtension_68_, 2);
v___x_70_ = l_Lean_TagDeclarationExtension_isTagged(v___x_67_, v_env_66_, v_declName_62_, v_asyncMode_69_);
v___x_71_ = lean_box(v___x_70_);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT void l_Lean_Meta_isRecursiveDefinition___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_62_ = stack[0].m_obj;
lean_object* v_a_63_ = stack[1].m_obj;
lean_object* v_res_73_;
v_res_73_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_62_, v_a_63_);
stack->m_obj
 = v_res_73_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___redArg___boxed(lean_object* v_declName_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_74_, v_a_75_);
lean_dec(v_a_75_);
return v_res_77_;
}
}
lean_object* l_Lean_Meta_isRecursiveDefinition(lean_object* v_declName_78_, lean_object* v_a_79_, lean_object* v_a_80_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_78_, v_a_80_);
return v___x_82_;
}
}
LEAN_EXPORT void l_Lean_Meta_isRecursiveDefinition_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_78_ = stack[0].m_obj;
lean_object* v_a_79_ = stack[1].m_obj;
lean_object* v_a_80_ = stack[2].m_obj;
lean_object* v_res_83_;
v_res_83_ = l_Lean_Meta_isRecursiveDefinition(v_declName_78_, v_a_79_, v_a_80_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRecursiveDefinition___boxed(lean_object* v_declName_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Meta_isRecursiveDefinition(v_declName_84_, v_a_85_, v_a_86_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
return v_res_88_;
}
}
lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_RecExt(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
