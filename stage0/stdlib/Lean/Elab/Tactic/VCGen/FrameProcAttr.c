// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.FrameProcAttr
// Imports: public import Lean.Elab.Tactic.VCGen.Context
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs;
lean_object* l_Lean_Elab_Tactic_VCGen_FrameProcs_insert(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Environment_evalConst___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknown constant '"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "VCGen"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "FrameProc"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__6_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__7_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(206, 175, 173, 61, 99, 140, 39, 150)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__7_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__6_value),LEAN_SCALAR_PTR_LITERAL(215, 105, 72, 137, 15, 249, 238, 46)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a `FrameProc`"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_toFrameProcEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_toFrameProcEntry___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "frameProcExt"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(206, 175, 173, 61, 99, 140, 39, 150)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(29, 42, 49, 58, 222, 49, 71, 101)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_frameProcExt;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "frameproc"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 4, 63, 122, 93, 234, 142, 166)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_addFrameProcAttr(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Attribute `["};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "]` cannot be erased"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(26, 120, 232, 197, 117, 221, 112, 15)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "FrameProcAttr"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(249, 112, 84, 103, 60, 189, 177, 186)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(220, 151, 145, 119, 179, 121, 34, 58)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(253, 200, 202, 65, 57, 232, 192, 233)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__11_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(203, 68, 244, 142, 162, 117, 135, 135)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__11_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__11_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__12_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__11_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(202, 107, 143, 117, 97, 167, 185, 186)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__12_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__12_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__13_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__12_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(193, 65, 214, 248, 163, 46, 94, 183)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__13_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__13_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__14_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__14_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__14_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__15_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__13_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__14_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(120, 207, 182, 10, 196, 119, 151, 55)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__15_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__15_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__16_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__16_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__16_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__17_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__15_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__16_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 37, 175, 152, 42, 232, 56, 149)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__17_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__17_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__18_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__17_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__2_value),LEAN_SCALAR_PTR_LITERAL(12, 197, 9, 40, 230, 56, 28, 99)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__18_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__18_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__19_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__18_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(198, 93, 73, 254, 42, 72, 75, 201)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__19_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__19_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__20_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__19_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(91, 133, 189, 86, 203, 98, 250, 50)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__20_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__20_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__21_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__20_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(92, 167, 192, 217, 53, 30, 153, 139)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__21_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__21_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__22_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__21_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 19, 86, 190, 233, 132, 211, 193)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__22_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__22_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__23_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__22_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1192303900) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(114, 245, 244, 99, 65, 180, 204, 144)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__23_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__23_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__24_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__24_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__24_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__25_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__23_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__24_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(253, 156, 53, 39, 115, 235, 197, 120)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__25_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__25_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__26_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__26_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__26_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__27_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__25_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__26_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(93, 20, 45, 107, 217, 232, 24, 126)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__27_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__27_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__28_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__27_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(48, 117, 254, 38, 60, 51, 194, 184)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__28_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__28_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__29_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___closed__1_value)} };
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__29_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__29_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__30_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "register a frame inference procedure for `vcgen`"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__30_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__30_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__31_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__28_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___closed__1_value),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__30_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__31_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__31_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__32_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__31_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__29_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__32_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__32_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___redArg(lean_object* v_e_1_){
_start:
{
if (lean_obj_tag(v_e_1_) == 0)
{
lean_object* v_a_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_11_; 
v_a_3_ = lean_ctor_get(v_e_1_, 0);
v_isSharedCheck_11_ = !lean_is_exclusive(v_e_1_);
if (v_isSharedCheck_11_ == 0)
{
v___x_5_ = v_e_1_;
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_a_3_);
lean_dec(v_e_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_11_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v___x_7_; lean_object* v___x_9_; 
v___x_7_ = lean_mk_io_user_error(v_a_3_);
if (v_isShared_6_ == 0)
{
lean_ctor_set_tag(v___x_5_, 1);
lean_ctor_set(v___x_5_, 0, v___x_7_);
v___x_9_ = v___x_5_;
goto v_reusejp_8_;
}
else
{
lean_object* v_reuseFailAlloc_10_; 
v_reuseFailAlloc_10_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_10_, 0, v___x_7_);
v___x_9_ = v_reuseFailAlloc_10_;
goto v_reusejp_8_;
}
v_reusejp_8_:
{
return v___x_9_;
}
}
}
else
{
lean_object* v_a_12_; lean_object* v___x_14_; uint8_t v_isShared_15_; uint8_t v_isSharedCheck_19_; 
v_a_12_ = lean_ctor_get(v_e_1_, 0);
v_isSharedCheck_19_ = !lean_is_exclusive(v_e_1_);
if (v_isSharedCheck_19_ == 0)
{
v___x_14_ = v_e_1_;
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
else
{
lean_inc(v_a_12_);
lean_dec(v_e_1_);
v___x_14_ = lean_box(0);
v_isShared_15_ = v_isSharedCheck_19_;
goto v_resetjp_13_;
}
v_resetjp_13_:
{
lean_object* v___x_17_; 
if (v_isShared_15_ == 0)
{
lean_ctor_set_tag(v___x_14_, 0);
v___x_17_ = v___x_14_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v_a_12_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v_res_20_;
v_res_20_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___redArg(v_e_1_);
stack->m_obj
 = v_res_20_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___redArg___boxed(lean_object* v_e_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___redArg(v_e_21_);
return v_res_23_;
}
}
lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0(lean_object* v_00_u03b1_24_, lean_object* v_e_25_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___redArg(v_e_25_);
return v___x_27_;
}
}
LEAN_EXPORT void l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_25_ = stack[1].m_obj;
lean_object* v_res_28_;
v_res_28_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0(lean_box(0), v_e_25_);
stack->m_obj
 = v_res_28_;
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___boxed(lean_object* v_00_u03b1_29_, lean_object* v_e_30_, lean_object* v_a_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0(v_00_u03b1_29_, v_e_30_);
return v_res_32_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl(lean_object* v_declName_48_, lean_object* v_a_49_){
_start:
{
lean_object* v_env_51_; lean_object* v_opts_52_; uint8_t v___x_53_; lean_object* v___x_54_; 
v_env_51_ = lean_ctor_get(v_a_49_, 0);
v_opts_52_ = lean_ctor_get(v_a_49_, 1);
v___x_53_ = 0;
lean_inc(v_declName_48_);
lean_inc_ref(v_env_51_);
v___x_54_ = l_Lean_Environment_find_x3f(v_env_51_, v_declName_48_, v___x_53_);
if (lean_obj_tag(v___x_54_) == 0)
{
lean_object* v___x_55_; uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_55_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__0));
v___x_56_ = 1;
v___x_57_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_48_, v___x_56_);
v___x_58_ = lean_string_append(v___x_55_, v___x_57_);
lean_dec_ref(v___x_57_);
v___x_59_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__1));
v___x_60_ = lean_string_append(v___x_58_, v___x_59_);
v___x_61_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
v___x_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
return v___x_62_;
}
else
{
lean_object* v_val_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_82_; 
v_val_63_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_82_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_82_ == 0)
{
v___x_65_ = v___x_54_;
v_isShared_66_ = v_isSharedCheck_82_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_val_63_);
lean_dec(v___x_54_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_82_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v___x_67_ = l_Lean_ConstantInfo_type(v_val_63_);
lean_dec(v_val_63_);
v___x_68_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__7));
v___x_69_ = l_Lean_Expr_isConstOf(v___x_67_, v___x_68_);
lean_dec_ref(v___x_67_);
if (v___x_69_ == 0)
{
lean_object* v___x_70_; uint8_t v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_70_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__8));
v___x_71_ = 1;
v___x_72_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_48_, v___x_71_);
v___x_73_ = lean_string_append(v___x_70_, v___x_72_);
lean_dec_ref(v___x_72_);
v___x_74_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__9));
v___x_75_ = lean_string_append(v___x_73_, v___x_74_);
if (v_isShared_66_ == 0)
{
lean_ctor_set_tag(v___x_65_, 18);
lean_ctor_set(v___x_65_, 0, v___x_75_);
v___x_77_ = v___x_65_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_75_);
v___x_77_ = v_reuseFailAlloc_79_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; 
v___x_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
return v___x_78_;
}
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_del_object(v___x_65_);
v___x_80_ = l_Lean_Environment_evalConst___redArg(v_env_51_, v_opts_52_, v_declName_48_, v___x_69_);
lean_dec(v_declName_48_);
v___x_81_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___redArg(v___x_80_);
return v___x_81_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_48_ = stack[0].m_obj;
lean_object* v_a_49_ = stack[1].m_obj;
lean_object* v_res_83_;
v_res_83_ = l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl(v_declName_48_, v_a_49_);
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___boxed(lean_object* v_declName_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl(v_declName_84_, v_a_85_);
lean_dec_ref(v_a_85_);
return v_res_87_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_toFrameProcEntry(lean_object* v_declName_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_91_; 
lean_inc(v_declName_88_);
v___x_91_ = l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl(v_declName_88_, v_a_89_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_100_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_100_ == 0)
{
v___x_94_ = v___x_91_;
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_a_92_);
lean_dec(v___x_91_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_100_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_96_, 0, v_declName_88_);
lean_ctor_set(v___x_96_, 1, v_a_92_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_96_);
v___x_98_ = v___x_94_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_96_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
else
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
lean_dec(v_declName_88_);
v_a_101_ = lean_ctor_get(v___x_91_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_91_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_91_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_91_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_toFrameProcEntry_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_88_ = stack[0].m_obj;
lean_object* v_a_89_ = stack[1].m_obj;
lean_object* v_res_109_;
v_res_109_ = l_Lean_Elab_Tactic_VCGen_toFrameProcEntry(v_declName_88_, v_a_89_);
stack->m_obj
 = v_res_109_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_toFrameProcEntry___boxed(lean_object* v_declName_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Elab_Tactic_VCGen_toFrameProcEntry(v_declName_110_, v_a_111_);
lean_dec_ref(v_a_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v___y_114_){
_start:
{
lean_inc_ref(v___y_114_);
return v___y_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v___y_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v___y_115_);
lean_dec_ref(v___y_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v_x_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_119_, 0, v_a_118_);
lean_inc_ref_n(v___x_119_, 2);
v___x_120_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
lean_ctor_set(v___x_120_, 2, v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v_x_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v_x_121_, v_a_122_);
lean_dec_ref(v_x_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v_s_124_, lean_object* v_x_125_){
_start:
{
lean_object* v_snd_126_; lean_object* v___x_127_; 
v_snd_126_ = lean_ctor_get(v_x_125_, 1);
lean_inc(v_snd_126_);
lean_dec_ref(v_x_125_);
v___x_127_ = l_Lean_Elab_Tactic_VCGen_FrameProcs_insert(v_s_124_, v_snd_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v_x_128_){
_start:
{
lean_object* v_fst_129_; 
v_fst_129_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_fst_129_);
return v_fst_129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v_x_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v_x_130_);
lean_dec_ref(v_x_130_);
return v_res_131_;
}
}
lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v_x_132_, lean_object* v_declName_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Elab_Tactic_VCGen_toFrameProcEntry(v_declName_133_, v___y_134_);
return v___x_136_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_x_132_ = stack[0].m_obj;
lean_object* v_declName_133_ = stack[1].m_obj;
lean_object* v___y_134_ = stack[2].m_obj;
lean_object* v_res_137_;
v_res_137_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v_x_132_, v_declName_133_, v___y_134_);
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v_x_138_, lean_object* v_declName_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v_x_138_, v_declName_139_, v___y_140_);
lean_dec_ref(v___y_140_);
lean_dec_ref(v_x_138_);
return v_res_142_;
}
}
lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v___x_143_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_145_, 0, v___x_143_);
return v___x_145_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_143_ = stack[0].m_obj;
lean_object* v_res_146_;
v_res_146_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v___x_143_);
stack->m_obj
 = v_res_146_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v___x_147_, lean_object* v___y_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v___x_147_);
return v_res_149_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = lean_box(0);
v___x_163_ = lean_unsigned_to_nat(16u);
v___x_164_ = lean_mk_array(v___x_163_, v___x_162_);
return v___x_164_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___x_166_ = lean_unsigned_to_nat(0u);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_168_; lean_object* v___f_169_; 
v___x_168_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___f_169_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_169_, 0, v___x_168_);
return v___f_169_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_170_; uint8_t v___x_171_; lean_object* v___f_172_; lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_170_ = lean_box(0);
v___x_171_ = 0;
v___f_172_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_173_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_174_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_175_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_176_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_177_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___x_178_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___x_179_ = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___f_177_);
lean_ctor_set(v___x_179_, 2, v___f_176_);
lean_ctor_set(v___x_179_, 3, v___f_175_);
lean_ctor_set(v___x_179_, 4, v___f_174_);
lean_ctor_set(v___x_179_, 5, v___f_173_);
lean_ctor_set(v___x_179_, 6, v___f_172_);
lean_ctor_set(v___x_179_, 7, v___x_170_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*8, v___x_171_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*8 + 1, v___x_171_);
return v___x_179_;
}
}
lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___x_182_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_183_;
v_res_183_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_();
stack->m_obj
 = v_res_183_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v_a_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_();
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg___lam__0(lean_object* v___x_186_, lean_object* v_toPure_187_, lean_object* v_____do__lift_188_){
_start:
{
lean_object* v___x_189_; lean_object* v_ext_190_; lean_object* v_toEnvExtension_191_; lean_object* v_asyncMode_192_; uint8_t v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_189_ = l_Lean_Elab_Tactic_VCGen_frameProcExt;
v_ext_190_ = lean_ctor_get(v___x_189_, 1);
v_toEnvExtension_191_ = lean_ctor_get(v_ext_190_, 0);
v_asyncMode_192_ = lean_ctor_get(v_toEnvExtension_191_, 2);
v___x_193_ = 0;
v___x_194_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_186_, v___x_189_, v_____do__lift_188_, v_asyncMode_192_, v___x_193_);
v___x_195_ = lean_apply_2(v_toPure_187_, lean_box(0), v___x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg___lam__0___boxed(lean_object* v___x_196_, lean_object* v_toPure_197_, lean_object* v_____do__lift_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg___lam__0(v___x_196_, v_toPure_197_, v_____do__lift_198_);
lean_dec_ref(v___x_196_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg(lean_object* v_inst_200_, lean_object* v_inst_201_){
_start:
{
lean_object* v_toApplicative_202_; lean_object* v_toBind_203_; lean_object* v_getEnv_204_; lean_object* v_toPure_205_; lean_object* v___x_206_; lean_object* v___f_207_; lean_object* v___x_208_; 
v_toApplicative_202_ = lean_ctor_get(v_inst_200_, 0);
lean_inc_ref(v_toApplicative_202_);
v_toBind_203_ = lean_ctor_get(v_inst_200_, 1);
lean_inc(v_toBind_203_);
lean_dec_ref(v_inst_200_);
v_getEnv_204_ = lean_ctor_get(v_inst_201_, 0);
lean_inc(v_getEnv_204_);
lean_dec_ref(v_inst_201_);
v_toPure_205_ = lean_ctor_get(v_toApplicative_202_, 1);
lean_inc(v_toPure_205_);
lean_dec_ref(v_toApplicative_202_);
v___x_206_ = l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs;
v___f_207_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_207_, 0, v___x_206_);
lean_closure_set(v___f_207_, 1, v_toPure_205_);
v___x_208_ = lean_apply_4(v_toBind_203_, lean_box(0), lean_box(0), v_getEnv_204_, v___f_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs(lean_object* v_m_209_, lean_object* v_inst_210_, lean_object* v_inst_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg(v_inst_210_, v_inst_211_);
return v___x_212_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_213_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0);
v___x_215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__1);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_216_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
return v___x_217_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg(lean_object* v_ext_218_, lean_object* v_b_219_, uint8_t v_kind_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_toCold_224_; lean_object* v_currNamespace_225_; lean_object* v___x_226_; lean_object* v_env_227_; lean_object* v_nextMacroScope_228_; lean_object* v_ngen_229_; lean_object* v_auxDeclNGen_230_; lean_object* v_traceState_231_; lean_object* v_recordedDeps_232_; lean_object* v_messages_233_; lean_object* v_infoState_234_; lean_object* v_snapshotTasks_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_247_; 
v_toCold_224_ = lean_ctor_get(v___y_221_, 0);
v_currNamespace_225_ = lean_ctor_get(v_toCold_224_, 4);
v___x_226_ = lean_st_ref_take(v___y_222_);
v_env_227_ = lean_ctor_get(v___x_226_, 0);
v_nextMacroScope_228_ = lean_ctor_get(v___x_226_, 1);
v_ngen_229_ = lean_ctor_get(v___x_226_, 2);
v_auxDeclNGen_230_ = lean_ctor_get(v___x_226_, 3);
v_traceState_231_ = lean_ctor_get(v___x_226_, 4);
v_recordedDeps_232_ = lean_ctor_get(v___x_226_, 6);
v_messages_233_ = lean_ctor_get(v___x_226_, 7);
v_infoState_234_ = lean_ctor_get(v___x_226_, 8);
v_snapshotTasks_235_ = lean_ctor_get(v___x_226_, 9);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_247_ == 0)
{
lean_object* v_unused_248_; 
v_unused_248_ = lean_ctor_get(v___x_226_, 5);
lean_dec(v_unused_248_);
v___x_237_ = v___x_226_;
v_isShared_238_ = v_isSharedCheck_247_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_snapshotTasks_235_);
lean_inc(v_infoState_234_);
lean_inc(v_messages_233_);
lean_inc(v_recordedDeps_232_);
lean_inc(v_traceState_231_);
lean_inc(v_auxDeclNGen_230_);
lean_inc(v_ngen_229_);
lean_inc(v_nextMacroScope_228_);
lean_inc(v_env_227_);
lean_dec(v___x_226_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_247_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_243_; 
v___x_239_ = lean_box(0);
lean_inc(v_currNamespace_225_);
v___x_240_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_227_, v_ext_218_, v_b_219_, v_kind_220_, v_currNamespace_225_);
v___x_241_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__2);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 5, v___x_241_);
lean_ctor_set(v___x_237_, 0, v___x_240_);
v___x_243_ = v___x_237_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v___x_240_);
lean_ctor_set(v_reuseFailAlloc_246_, 1, v_nextMacroScope_228_);
lean_ctor_set(v_reuseFailAlloc_246_, 2, v_ngen_229_);
lean_ctor_set(v_reuseFailAlloc_246_, 3, v_auxDeclNGen_230_);
lean_ctor_set(v_reuseFailAlloc_246_, 4, v_traceState_231_);
lean_ctor_set(v_reuseFailAlloc_246_, 5, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_246_, 6, v_recordedDeps_232_);
lean_ctor_set(v_reuseFailAlloc_246_, 7, v_messages_233_);
lean_ctor_set(v_reuseFailAlloc_246_, 8, v_infoState_234_);
lean_ctor_set(v_reuseFailAlloc_246_, 9, v_snapshotTasks_235_);
v___x_243_ = v_reuseFailAlloc_246_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_st_ref_put(v___y_222_, v___x_243_);
v___x_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_245_, 0, v___x_239_);
return v___x_245_;
}
}
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_218_ = stack[0].m_obj;
lean_object* v_b_219_ = stack[1].m_obj;
uint8_t v_kind_220_ = stack[2].m_num;
lean_object* v___y_221_ = stack[3].m_obj;
lean_object* v___y_222_ = stack[4].m_obj;
lean_object* v_res_249_;
v_res_249_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg(v_ext_218_, v_b_219_, v_kind_220_, v___y_221_, v___y_222_);
stack->m_obj
 = v_res_249_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___boxed(lean_object* v_ext_250_, lean_object* v_b_251_, lean_object* v_kind_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
uint8_t v_kind_boxed_256_; lean_object* v_res_257_; 
v_kind_boxed_256_ = lean_unbox(v_kind_252_);
v_res_257_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg(v_ext_250_, v_b_251_, v_kind_boxed_256_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
return v_res_257_;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0(lean_object* v_00_u03b1_258_, lean_object* v_00_u03b2_259_, lean_object* v_00_u03c3_260_, lean_object* v_ext_261_, lean_object* v_b_262_, uint8_t v_kind_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg(v_ext_261_, v_b_262_, v_kind_263_, v___y_264_, v___y_265_);
return v___x_267_;
}
}
LEAN_EXPORT void l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ext_261_ = stack[3].m_obj;
lean_object* v_b_262_ = stack[4].m_obj;
uint8_t v_kind_263_ = stack[5].m_num;
lean_object* v___y_264_ = stack[6].m_obj;
lean_object* v___y_265_ = stack[7].m_obj;
lean_object* v_res_268_;
v_res_268_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0(lean_box(0), lean_box(0), lean_box(0), v_ext_261_, v_b_262_, v_kind_263_, v___y_264_, v___y_265_);
stack->m_obj
 = v_res_268_;
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___boxed(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_00_u03c3_271_, lean_object* v_ext_272_, lean_object* v_b_273_, lean_object* v_kind_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
uint8_t v_kind_boxed_278_; lean_object* v_res_279_; 
v_kind_boxed_278_ = lean_unbox(v_kind_274_);
v_res_279_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0(v_00_u03b1_269_, v_00_u03b2_270_, v_00_u03c3_271_, v_ext_272_, v_b_273_, v_kind_boxed_278_, v___y_275_, v___y_276_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_279_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_addFrameProcAttr(lean_object* v_declName_283_, uint8_t v_kind_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___closed__1));
lean_inc(v_declName_283_);
v___x_289_ = l_Lean_ensureAttrDeclIsMeta(v___x_288_, v_declName_283_, v_kind_284_, v_a_285_, v_a_286_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_317_; 
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v___x_289_, 0);
lean_dec(v_unused_318_);
v___x_291_ = v___x_289_;
v_isShared_292_ = v_isSharedCheck_317_;
goto v_resetjp_290_;
}
else
{
lean_dec(v___x_289_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_317_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v_env_294_; lean_object* v_ref_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_293_ = lean_st_ref_get(v_a_286_);
v_env_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc_ref(v_env_294_);
lean_dec(v___x_293_);
v_ref_295_ = lean_ctor_get(v_a_285_, 2);
v___x_296_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_285_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v_env_294_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
lean_inc(v_declName_283_);
v___x_298_ = l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl(v_declName_283_, v___x_297_);
lean_dec_ref_known(v___x_297_, 2);
if (lean_obj_tag(v___x_298_) == 0)
{
lean_object* v_a_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
lean_del_object(v___x_291_);
v_a_299_ = lean_ctor_get(v___x_298_, 0);
lean_inc(v_a_299_);
lean_dec_ref_known(v___x_298_, 1);
v___x_300_ = l_Lean_Elab_Tactic_VCGen_frameProcExt;
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v_declName_283_);
lean_ctor_set(v___x_301_, 1, v_a_299_);
v___x_302_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg(v___x_300_, v___x_301_, v_kind_284_, v_a_285_, v_a_286_);
return v___x_302_;
}
else
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_316_; 
lean_dec(v_declName_283_);
v_a_303_ = lean_ctor_get(v___x_298_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_298_);
if (v_isSharedCheck_316_ == 0)
{
v___x_305_ = v___x_298_;
v_isShared_306_ = v_isSharedCheck_316_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_298_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_316_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_309_; 
v___x_307_ = lean_io_error_to_string(v_a_303_);
if (v_isShared_292_ == 0)
{
lean_ctor_set_tag(v___x_291_, 3);
lean_ctor_set(v___x_291_, 0, v___x_307_);
v___x_309_ = v___x_291_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_307_);
v___x_309_ = v_reuseFailAlloc_315_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_310_ = l_Lean_MessageData_ofFormat(v___x_309_);
lean_inc(v_ref_295_);
v___x_311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_311_, 0, v_ref_295_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_311_);
v___x_313_ = v___x_305_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
}
else
{
lean_dec(v_declName_283_);
return v___x_289_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_addFrameProcAttr_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_283_ = stack[0].m_obj;
uint8_t v_kind_284_ = stack[1].m_num;
lean_object* v_a_285_ = stack[2].m_obj;
lean_object* v_a_286_ = stack[3].m_obj;
lean_object* v_res_319_;
v_res_319_ = l_Lean_Elab_Tactic_VCGen_addFrameProcAttr(v_declName_283_, v_kind_284_, v_a_285_, v_a_286_);
stack->m_obj
 = v_res_319_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___boxed(lean_object* v_declName_320_, lean_object* v_kind_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
uint8_t v_kind_boxed_325_; lean_object* v_res_326_; 
v_kind_boxed_325_ = lean_unbox(v_kind_321_);
v_res_326_ = l_Lean_Elab_Tactic_VCGen_addFrameProcAttr(v_declName_320_, v_kind_boxed_325_, v_a_322_, v_a_323_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
return v_res_326_;
}
}
lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(lean_object* v_declName_327_, lean_object* v___stx_328_, uint8_t v_kind_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_Elab_Tactic_VCGen_addFrameProcAttr(v_declName_327_, v_kind_329_, v___y_330_, v___y_331_);
return v___x_333_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_327_ = stack[0].m_obj;
lean_object* v___stx_328_ = stack[1].m_obj;
uint8_t v_kind_329_ = stack[2].m_num;
lean_object* v___y_330_ = stack[3].m_obj;
lean_object* v___y_331_ = stack[4].m_obj;
lean_object* v_res_334_;
v_res_334_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(v_declName_327_, v___stx_328_, v_kind_329_, v___y_330_, v___y_331_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object* v_declName_335_, lean_object* v___stx_336_, lean_object* v_kind_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
uint8_t v_kind_boxed_341_; lean_object* v_res_342_; 
v_kind_boxed_341_ = lean_unbox(v_kind_337_);
v_res_342_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(v_declName_335_, v___stx_336_, v_kind_boxed_341_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___stx_336_);
return v_res_342_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0);
v___x_344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_345_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_346_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
lean_ctor_set(v___x_348_, 2, v___x_347_);
lean_ctor_set(v___x_348_, 3, v___x_347_);
lean_ctor_set(v___x_348_, 4, v___x_346_);
lean_ctor_set(v___x_348_, 5, v___x_346_);
lean_ctor_set(v___x_348_, 6, v___x_346_);
lean_ctor_set(v___x_348_, 7, v___x_346_);
lean_ctor_set(v___x_348_, 8, v___x_346_);
lean_ctor_set(v___x_348_, 9, v___x_346_);
lean_ctor_set(v___x_348_, 10, v___x_346_);
lean_ctor_set(v___x_348_, 11, v___x_345_);
return v___x_348_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = lean_unsigned_to_nat(32u);
v___x_350_ = lean_mk_empty_array_with_capacity(v___x_349_);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
size_t v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_352_ = ((size_t)5ULL);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_unsigned_to_nat(32u);
v___x_355_ = lean_mk_empty_array_with_capacity(v___x_354_);
v___x_356_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_357_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_357_, 0, v___x_356_);
lean_ctor_set(v___x_357_, 1, v___x_355_);
lean_ctor_set(v___x_357_, 2, v___x_353_);
lean_ctor_set(v___x_357_, 3, v___x_353_);
lean_ctor_set_usize(v___x_357_, 4, v___x_352_);
return v___x_357_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_358_ = lean_box(1);
v___x_359_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_360_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_361_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v___x_359_);
lean_ctor_set(v___x_361_, 2, v___x_358_);
return v___x_361_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v___x_366_; lean_object* v_toCold_367_; lean_object* v_env_368_; lean_object* v_options_369_; uint8_t v___x_370_; lean_object* v_env_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_366_ = lean_st_ref_get(v___y_364_);
v_toCold_367_ = lean_ctor_get(v___y_363_, 0);
v_env_368_ = lean_ctor_get(v___x_366_, 0);
lean_inc_ref(v_env_368_);
lean_dec(v___x_366_);
v_options_369_ = lean_ctor_get(v_toCold_367_, 2);
v___x_370_ = 0;
v_env_371_ = l_Lean_Environment_setRecordingDeps(v_env_368_, v___x_370_);
v___x_372_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_373_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4);
lean_inc_ref(v_options_369_);
v___x_374_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_374_, 0, v_env_371_);
lean_ctor_set(v___x_374_, 1, v___x_372_);
lean_ctor_set(v___x_374_, 2, v___x_373_);
lean_ctor_set(v___x_374_, 3, v_options_369_);
v___x_375_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v_msgData_362_);
v___x_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
return v___x_376_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_362_ = stack[0].m_obj;
lean_object* v___y_363_ = stack[1].m_obj;
lean_object* v___y_364_ = stack[2].m_obj;
lean_object* v_res_377_;
v_res_377_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0(v_msgData_362_, v___y_363_, v___y_364_);
stack->m_obj
 = v_res_377_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0(v_msgData_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_382_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v_ref_387_; lean_object* v___x_388_; lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_397_; 
v_ref_387_ = lean_ctor_get(v___y_384_, 2);
v___x_388_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0(v_msg_383_, v___y_384_, v___y_385_);
v_a_389_ = lean_ctor_get(v___x_388_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_388_);
if (v_isSharedCheck_397_ == 0)
{
v___x_391_ = v___x_388_;
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_388_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_397_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; lean_object* v___x_395_; 
lean_inc(v_ref_387_);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v_ref_387_);
lean_ctor_set(v___x_393_, 1, v_a_389_);
if (v_isShared_392_ == 0)
{
lean_ctor_set_tag(v___x_391_, 1);
lean_ctor_set(v___x_391_, 0, v___x_393_);
v___x_395_ = v___x_391_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_383_ = stack[0].m_obj;
lean_object* v___y_384_ = stack[1].m_obj;
lean_object* v___y_385_ = stack[2].m_obj;
lean_object* v_res_398_;
v_res_398_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(v_msg_383_, v___y_384_, v___y_385_);
stack->m_obj
 = v_res_398_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(v_msg_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
return v_res_403_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_));
v___x_406_ = l_Lean_stringToMessageData(v___x_405_);
return v___x_406_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_));
v___x_409_ = l_Lean_stringToMessageData(v___x_408_);
return v___x_409_;
}
}
lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(lean_object* v___x_410_, lean_object* v_decl_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_415_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_);
v___x_416_ = l_Lean_MessageData_ofName(v___x_410_);
v___x_417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_417_, 0, v___x_415_);
lean_ctor_set(v___x_417_, 1, v___x_416_);
v___x_418_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_);
v___x_419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_417_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(v___x_419_, v___y_412_, v___y_413_);
return v___x_420_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_410_ = stack[0].m_obj;
lean_object* v_decl_411_ = stack[1].m_obj;
lean_object* v___y_412_ = stack[2].m_obj;
lean_object* v___y_413_ = stack[3].m_obj;
lean_object* v_res_421_;
v_res_421_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(v___x_410_, v_decl_411_, v___y_412_, v___y_413_);
stack->m_obj
 = v_res_421_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object* v___x_422_, lean_object* v_decl_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(v___x_422_, v_decl_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v_decl_423_);
return v_res_427_;
}
}
lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__32_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_));
v___x_515_ = l_Lean_registerBuiltinAttribute(v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_516_;
v_res_516_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_();
stack->m_obj
 = v_res_516_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_();
return v_res_518_;
}
}
lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_519_, lean_object* v_msg_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(v_msg_520_, v___y_521_, v___y_522_);
return v___x_524_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_520_ = stack[1].m_obj;
lean_object* v___y_521_ = stack[2].m_obj;
lean_object* v___y_522_ = stack[3].m_obj;
lean_object* v_res_525_;
v_res_525_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0(lean_box(0), v_msg_520_, v___y_521_, v___y_522_);
stack->m_obj
 = v_res_525_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_526_, lean_object* v_msg_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0(v_00_u03b1_526_, v_msg_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
return v_res_531_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_FrameProcAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_VCGen_frameProcExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_VCGen_frameProcExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_FrameProcAttr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_FrameProcAttr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_FrameProcAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_FrameProcAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_FrameProcAttr(builtin);
}
#ifdef __cplusplus
}
#endif
