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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_ensureAttrDeclIsMeta(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
static lean_once_cell_t l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__11_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__11_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_;
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
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5;
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___redArg(lean_object* v_e_1_){
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
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___redArg___boxed(lean_object* v_e_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___redArg(v_e_20_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0(lean_object* v_00_u03b1_23_, lean_object* v_e_24_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___redArg(v_e_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___boxed(lean_object* v_00_u03b1_27_, lean_object* v_e_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0(v_00_u03b1_27_, v_e_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl(lean_object* v_declName_46_, lean_object* v_a_47_){
_start:
{
lean_object* v_env_49_; lean_object* v_opts_50_; uint8_t v___x_51_; lean_object* v___x_52_; 
v_env_49_ = lean_ctor_get(v_a_47_, 0);
v_opts_50_ = lean_ctor_get(v_a_47_, 1);
v___x_51_ = 0;
lean_inc(v_declName_46_);
lean_inc_ref(v_env_49_);
v___x_52_ = l_Lean_Environment_find_x3f(v_env_49_, v_declName_46_, v___x_51_);
if (lean_obj_tag(v___x_52_) == 0)
{
lean_object* v___x_53_; uint8_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_53_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__0));
v___x_54_ = 1;
v___x_55_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_46_, v___x_54_);
v___x_56_ = lean_string_append(v___x_53_, v___x_55_);
lean_dec_ref(v___x_55_);
v___x_57_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__1));
v___x_58_ = lean_string_append(v___x_56_, v___x_57_);
v___x_59_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
v___x_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
else
{
lean_object* v_val_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_80_; 
v_val_61_ = lean_ctor_get(v___x_52_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_52_);
if (v_isSharedCheck_80_ == 0)
{
v___x_63_ = v___x_52_;
v_isShared_64_ = v_isSharedCheck_80_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_val_61_);
lean_dec(v___x_52_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_80_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v___x_65_ = l_Lean_ConstantInfo_type(v_val_61_);
lean_dec(v_val_61_);
v___x_66_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__7));
v___x_67_ = l_Lean_Expr_isConstOf(v___x_65_, v___x_66_);
lean_dec_ref(v___x_65_);
if (v___x_67_ == 0)
{
lean_object* v___x_68_; uint8_t v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_75_; 
v___x_68_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__8));
v___x_69_ = 1;
v___x_70_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_declName_46_, v___x_69_);
v___x_71_ = lean_string_append(v___x_68_, v___x_70_);
lean_dec_ref(v___x_70_);
v___x_72_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___closed__9));
v___x_73_ = lean_string_append(v___x_71_, v___x_72_);
if (v_isShared_64_ == 0)
{
lean_ctor_set_tag(v___x_63_, 18);
lean_ctor_set(v___x_63_, 0, v___x_73_);
v___x_75_ = v___x_63_;
goto v_reusejp_74_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v___x_73_);
v___x_75_ = v_reuseFailAlloc_77_;
goto v_reusejp_74_;
}
v_reusejp_74_:
{
lean_object* v___x_76_; 
v___x_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_del_object(v___x_63_);
v___x_78_ = l_Lean_Environment_evalConst___redArg(v_env_49_, v_opts_50_, v_declName_46_, v___x_67_);
lean_dec(v_declName_46_);
v___x_79_ = l_IO_ofExcept___at___00Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl_spec__0___redArg(v___x_78_);
return v___x_79_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl___boxed(lean_object* v_declName_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl(v_declName_81_, v_a_82_);
lean_dec_ref(v_a_82_);
return v_res_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_toFrameProcEntry(lean_object* v_declName_85_, lean_object* v_a_86_){
_start:
{
lean_object* v___x_88_; 
lean_inc(v_declName_85_);
v___x_88_ = l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl(v_declName_85_, v_a_86_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_97_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_97_ == 0)
{
v___x_91_ = v___x_88_;
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_93_, 0, v_declName_85_);
lean_ctor_set(v___x_93_, 1, v_a_89_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_93_);
v___x_95_ = v___x_91_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
else
{
lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_105_; 
lean_dec(v_declName_85_);
v_a_98_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_105_ == 0)
{
v___x_100_ = v___x_88_;
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_dec(v___x_88_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_105_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_a_98_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
return v___x_103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_toFrameProcEntry___boxed(lean_object* v_declName_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = l_Lean_Elab_Tactic_VCGen_toFrameProcEntry(v_declName_106_, v_a_107_);
lean_dec_ref(v_a_107_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v___y_110_){
_start:
{
lean_inc_ref(v___y_110_);
return v___y_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v___y_111_);
lean_dec_ref(v___y_111_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v_x_113_, lean_object* v_a_114_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_115_, 0, v_a_114_);
lean_inc_ref_n(v___x_115_, 2);
v___x_116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___x_115_);
lean_ctor_set(v___x_116_, 2, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v_x_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v_x_117_, v_a_118_);
lean_dec_ref(v_x_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v_s_120_, lean_object* v_x_121_){
_start:
{
lean_object* v_snd_122_; lean_object* v___x_123_; 
v_snd_122_ = lean_ctor_get(v_x_121_, 1);
lean_inc(v_snd_122_);
lean_dec_ref(v_x_121_);
v___x_123_ = l_Lean_Elab_Tactic_VCGen_FrameProcs_insert(v_s_120_, v_snd_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v_x_124_){
_start:
{
lean_object* v_fst_125_; 
v_fst_125_ = lean_ctor_get(v_x_124_, 0);
lean_inc(v_fst_125_);
return v_fst_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v_x_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v_x_126_);
lean_dec_ref(v_x_126_);
return v_res_127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v_x_128_, lean_object* v_declName_129_, lean_object* v___y_130_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_Elab_Tactic_VCGen_toFrameProcEntry(v_declName_129_, v___y_130_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v_x_133_, lean_object* v_declName_134_, lean_object* v___y_135_, lean_object* v___y_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v_x_133_, v_declName_134_, v___y_135_);
lean_dec_ref(v___y_135_);
lean_dec_ref(v_x_133_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(lean_object* v___x_138_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_140_, 0, v___x_138_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v___x_141_, lean_object* v___y_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(v___x_141_);
return v_res_143_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_156_; lean_object* v___x_157_; 
v_cellCount_156_ = lean_unsigned_to_nat(16u);
v___x_157_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_156_);
return v___x_157_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_158_; lean_object* v___x_159_; 
v_cellCount_158_ = lean_unsigned_to_nat(16u);
v___x_159_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_158_);
return v___x_159_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_160_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___x_161_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_161_);
lean_ctor_set(v___x_163_, 2, v___x_160_);
return v___x_163_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_164_; lean_object* v___f_165_; 
v___x_164_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___f_165_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_165_, 0, v___x_164_);
return v___f_165_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__11_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___f_169_; lean_object* v___f_170_; lean_object* v___f_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___f_166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_167_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_168_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_169_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_171_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___x_172_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___x_173_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___f_171_);
lean_ctor_set(v___x_173_, 2, v___f_170_);
lean_ctor_set(v___x_173_, 3, v___f_169_);
lean_ctor_set(v___x_173_, 4, v___f_168_);
lean_ctor_set(v___x_173_, 5, v___f_167_);
lean_ctor_set(v___x_173_, 6, v___f_166_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__11_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__11_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__11_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___x_176_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_();
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg___lam__0(lean_object* v___x_179_, lean_object* v_toPure_180_, lean_object* v_____do__lift_181_){
_start:
{
lean_object* v___x_182_; lean_object* v_ext_183_; lean_object* v_toEnvExtension_184_; lean_object* v_asyncMode_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_182_ = l_Lean_Elab_Tactic_VCGen_frameProcExt;
v_ext_183_ = lean_ctor_get(v___x_182_, 1);
v_toEnvExtension_184_ = lean_ctor_get(v_ext_183_, 0);
v_asyncMode_185_ = lean_ctor_get(v_toEnvExtension_184_, 2);
v___x_186_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_179_, v___x_182_, v_____do__lift_181_, v_asyncMode_185_);
v___x_187_ = lean_apply_2(v_toPure_180_, lean_box(0), v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg___lam__0___boxed(lean_object* v___x_188_, lean_object* v_toPure_189_, lean_object* v_____do__lift_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg___lam__0(v___x_188_, v_toPure_189_, v_____do__lift_190_);
lean_dec_ref(v___x_188_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg(lean_object* v_inst_192_, lean_object* v_inst_193_){
_start:
{
lean_object* v_toApplicative_194_; lean_object* v_toBind_195_; lean_object* v_getEnv_196_; lean_object* v_toPure_197_; lean_object* v___x_198_; lean_object* v___f_199_; lean_object* v___x_200_; 
v_toApplicative_194_ = lean_ctor_get(v_inst_192_, 0);
lean_inc_ref(v_toApplicative_194_);
v_toBind_195_ = lean_ctor_get(v_inst_192_, 1);
lean_inc(v_toBind_195_);
lean_dec_ref(v_inst_192_);
v_getEnv_196_ = lean_ctor_get(v_inst_193_, 0);
lean_inc(v_getEnv_196_);
lean_dec_ref(v_inst_193_);
v_toPure_197_ = lean_ctor_get(v_toApplicative_194_, 1);
lean_inc(v_toPure_197_);
lean_dec_ref(v_toApplicative_194_);
v___x_198_ = l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs;
v___f_199_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_199_, 0, v___x_198_);
lean_closure_set(v___f_199_, 1, v_toPure_197_);
v___x_200_ = lean_apply_4(v_toBind_195_, lean_box(0), lean_box(0), v_getEnv_196_, v___f_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs(lean_object* v_m_201_, lean_object* v_inst_202_, lean_object* v_inst_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg(v_inst_202_, v_inst_203_);
return v___x_204_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_205_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0);
v___x_207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
return v___x_207_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__1);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg(lean_object* v_ext_210_, lean_object* v_b_211_, uint8_t v_kind_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_currNamespace_216_; lean_object* v___x_217_; lean_object* v_env_218_; lean_object* v_nextMacroScope_219_; lean_object* v_ngen_220_; lean_object* v_auxDeclNGen_221_; lean_object* v_traceState_222_; lean_object* v_messages_223_; lean_object* v_infoState_224_; lean_object* v_snapshotTasks_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_237_; 
v_currNamespace_216_ = lean_ctor_get(v___y_213_, 6);
v___x_217_ = lean_st_ref_take(v___y_214_);
v_env_218_ = lean_ctor_get(v___x_217_, 0);
v_nextMacroScope_219_ = lean_ctor_get(v___x_217_, 1);
v_ngen_220_ = lean_ctor_get(v___x_217_, 2);
v_auxDeclNGen_221_ = lean_ctor_get(v___x_217_, 3);
v_traceState_222_ = lean_ctor_get(v___x_217_, 4);
v_messages_223_ = lean_ctor_get(v___x_217_, 6);
v_infoState_224_ = lean_ctor_get(v___x_217_, 7);
v_snapshotTasks_225_ = lean_ctor_get(v___x_217_, 8);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_237_ == 0)
{
lean_object* v_unused_238_; 
v_unused_238_ = lean_ctor_get(v___x_217_, 5);
lean_dec(v_unused_238_);
v___x_227_ = v___x_217_;
v_isShared_228_ = v_isSharedCheck_237_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_snapshotTasks_225_);
lean_inc(v_infoState_224_);
lean_inc(v_messages_223_);
lean_inc(v_traceState_222_);
lean_inc(v_auxDeclNGen_221_);
lean_inc(v_ngen_220_);
lean_inc(v_nextMacroScope_219_);
lean_inc(v_env_218_);
lean_dec(v___x_217_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_237_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_232_; 
lean_inc(v_currNamespace_216_);
v___x_229_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_218_, v_ext_210_, v_b_211_, v_kind_212_, v_currNamespace_216_);
v___x_230_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__2);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 5, v___x_230_);
lean_ctor_set(v___x_227_, 0, v___x_229_);
v___x_232_ = v___x_227_;
goto v_reusejp_231_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_nextMacroScope_219_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_ngen_220_);
lean_ctor_set(v_reuseFailAlloc_236_, 3, v_auxDeclNGen_221_);
lean_ctor_set(v_reuseFailAlloc_236_, 4, v_traceState_222_);
lean_ctor_set(v_reuseFailAlloc_236_, 5, v___x_230_);
lean_ctor_set(v_reuseFailAlloc_236_, 6, v_messages_223_);
lean_ctor_set(v_reuseFailAlloc_236_, 7, v_infoState_224_);
lean_ctor_set(v_reuseFailAlloc_236_, 8, v_snapshotTasks_225_);
v___x_232_ = v_reuseFailAlloc_236_;
goto v_reusejp_231_;
}
v_reusejp_231_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_233_ = lean_st_ref_put(v___y_214_, v___x_232_);
v___x_234_ = lean_box(0);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___boxed(lean_object* v_ext_239_, lean_object* v_b_240_, lean_object* v_kind_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
uint8_t v_kind_boxed_245_; lean_object* v_res_246_; 
v_kind_boxed_245_ = lean_unbox(v_kind_241_);
v_res_246_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg(v_ext_239_, v_b_240_, v_kind_boxed_245_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0(lean_object* v_00_u03b1_247_, lean_object* v_00_u03b2_248_, lean_object* v_00_u03c3_249_, lean_object* v_ext_250_, lean_object* v_b_251_, uint8_t v_kind_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg(v_ext_250_, v_b_251_, v_kind_252_, v___y_253_, v___y_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___boxed(lean_object* v_00_u03b1_257_, lean_object* v_00_u03b2_258_, lean_object* v_00_u03c3_259_, lean_object* v_ext_260_, lean_object* v_b_261_, lean_object* v_kind_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
uint8_t v_kind_boxed_266_; lean_object* v_res_267_; 
v_kind_boxed_266_ = lean_unbox(v_kind_262_);
v_res_267_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0(v_00_u03b1_257_, v_00_u03b2_258_, v_00_u03c3_259_, v_ext_260_, v_b_261_, v_kind_boxed_266_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_addFrameProcAttr(lean_object* v_declName_271_, uint8_t v_kind_272_, lean_object* v_a_273_, lean_object* v_a_274_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___closed__1));
lean_inc(v_declName_271_);
v___x_277_ = l_Lean_ensureAttrDeclIsMeta(v___x_276_, v_declName_271_, v_kind_272_, v_a_273_, v_a_274_);
if (lean_obj_tag(v___x_277_) == 0)
{
lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_305_; 
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_277_);
if (v_isSharedCheck_305_ == 0)
{
lean_object* v_unused_306_; 
v_unused_306_ = lean_ctor_get(v___x_277_, 0);
lean_dec(v_unused_306_);
v___x_279_ = v___x_277_;
v_isShared_280_ = v_isSharedCheck_305_;
goto v_resetjp_278_;
}
else
{
lean_dec(v___x_277_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_305_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v_env_282_; lean_object* v_options_283_; lean_object* v_ref_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_281_ = lean_st_ref_get(v_a_274_);
v_env_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc_ref(v_env_282_);
lean_dec(v___x_281_);
v_options_283_ = lean_ctor_get(v_a_273_, 2);
v_ref_284_ = lean_ctor_get(v_a_273_, 5);
lean_inc_ref(v_options_283_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v_env_282_);
lean_ctor_set(v___x_285_, 1, v_options_283_);
lean_inc(v_declName_271_);
v___x_286_ = l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl(v_declName_271_, v___x_285_);
lean_dec_ref_known(v___x_285_, 2);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
lean_del_object(v___x_279_);
v_a_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_a_287_);
lean_dec_ref_known(v___x_286_, 1);
v___x_288_ = l_Lean_Elab_Tactic_VCGen_frameProcExt;
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_declName_271_);
lean_ctor_set(v___x_289_, 1, v_a_287_);
v___x_290_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg(v___x_288_, v___x_289_, v_kind_272_, v_a_273_, v_a_274_);
return v___x_290_;
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_304_; 
lean_dec(v_declName_271_);
v_a_291_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_304_ == 0)
{
v___x_293_ = v___x_286_;
v_isShared_294_ = v_isSharedCheck_304_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_286_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_304_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_297_; 
v___x_295_ = lean_io_error_to_string(v_a_291_);
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 3);
lean_ctor_set(v___x_279_, 0, v___x_295_);
v___x_297_ = v___x_279_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_295_);
v___x_297_ = v_reuseFailAlloc_303_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_298_ = l_Lean_MessageData_ofFormat(v___x_297_);
lean_inc(v_ref_284_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_ref_284_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_299_);
v___x_301_ = v___x_293_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
}
else
{
lean_dec(v_declName_271_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___boxed(lean_object* v_declName_307_, lean_object* v_kind_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_){
_start:
{
uint8_t v_kind_boxed_312_; lean_object* v_res_313_; 
v_kind_boxed_312_ = lean_unbox(v_kind_308_);
v_res_313_ = l_Lean_Elab_Tactic_VCGen_addFrameProcAttr(v_declName_307_, v_kind_boxed_312_, v_a_309_, v_a_310_);
lean_dec(v_a_310_);
lean_dec_ref(v_a_309_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(lean_object* v_declName_314_, lean_object* v___stx_315_, uint8_t v_kind_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Elab_Tactic_VCGen_addFrameProcAttr(v_declName_314_, v_kind_316_, v___y_317_, v___y_318_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object* v_declName_321_, lean_object* v___stx_322_, lean_object* v_kind_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
uint8_t v_kind_boxed_327_; lean_object* v_res_328_; 
v_kind_boxed_327_ = lean_unbox(v_kind_323_);
v_res_328_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(v_declName_321_, v___stx_322_, v_kind_boxed_327_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___stx_322_);
return v_res_328_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_329_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
return v___x_331_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_333_ = lean_unsigned_to_nat(0u);
v___x_334_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
lean_ctor_set(v___x_334_, 2, v___x_333_);
lean_ctor_set(v___x_334_, 3, v___x_333_);
lean_ctor_set(v___x_334_, 4, v___x_332_);
lean_ctor_set(v___x_334_, 5, v___x_332_);
lean_ctor_set(v___x_334_, 6, v___x_332_);
lean_ctor_set(v___x_334_, 7, v___x_332_);
lean_ctor_set(v___x_334_, 8, v___x_332_);
lean_ctor_set(v___x_334_, 9, v___x_332_);
lean_ctor_set(v___x_334_, 10, v___x_332_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = lean_unsigned_to_nat(32u);
v___x_336_ = lean_mk_empty_array_with_capacity(v___x_335_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_338_ = ((size_t)5ULL);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_unsigned_to_nat(32u);
v___x_341_ = lean_mk_empty_array_with_capacity(v___x_340_);
v___x_342_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_343_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
lean_ctor_set(v___x_343_, 2, v___x_339_);
lean_ctor_set(v___x_343_, 3, v___x_339_);
lean_ctor_set_usize(v___x_343_, 4, v___x_338_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_344_ = lean_box(1);
v___x_345_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_346_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v___x_345_);
lean_ctor_set(v___x_347_, 2, v___x_344_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v___x_352_; lean_object* v_env_353_; lean_object* v_options_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_352_ = lean_st_ref_get(v___y_350_);
v_env_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc_ref(v_env_353_);
lean_dec(v___x_352_);
v_options_354_ = lean_ctor_get(v___y_349_, 2);
v___x_355_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_356_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_354_);
v___x_357_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_357_, 0, v_env_353_);
lean_ctor_set(v___x_357_, 1, v___x_355_);
lean_ctor_set(v___x_357_, 2, v___x_356_);
lean_ctor_set(v___x_357_, 3, v_options_354_);
v___x_358_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v_msgData_348_);
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0(v_msgData_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
return v_res_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v_ref_369_; lean_object* v___x_370_; lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_379_; 
v_ref_369_ = lean_ctor_get(v___y_366_, 5);
v___x_370_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0(v_msg_365_, v___y_366_, v___y_367_);
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_379_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_377_; 
lean_inc(v_ref_369_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v_ref_369_);
lean_ctor_set(v___x_375_, 1, v_a_371_);
if (v_isShared_374_ == 0)
{
lean_ctor_set_tag(v___x_373_, 1);
lean_ctor_set(v___x_373_, 0, v___x_375_);
v___x_377_ = v___x_373_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(v_msg_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
return v_res_384_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_));
v___x_387_ = l_Lean_stringToMessageData(v___x_386_);
return v___x_387_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_));
v___x_390_ = l_Lean_stringToMessageData(v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(lean_object* v___x_391_, lean_object* v_decl_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_396_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_);
v___x_397_ = l_Lean_MessageData_ofName(v___x_391_);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_);
v___x_400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(v___x_400_, v___y_393_, v___y_394_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object* v___x_402_, lean_object* v_decl_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(v___x_402_, v_decl_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v_decl_403_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_494_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__32_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_));
v___x_495_ = l_Lean_registerBuiltinAttribute(v___x_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object* v_a_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_();
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_498_, lean_object* v_msg_499_, lean_object* v___y_500_, lean_object* v___y_501_){
_start:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(v_msg_499_, v___y_500_, v___y_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_504_, lean_object* v_msg_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0(v_00_u03b1_504_, v_msg_505_, v___y_506_, v___y_507_);
lean_dec(v___y_507_);
lean_dec_ref(v___y_506_);
return v_res_509_;
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
