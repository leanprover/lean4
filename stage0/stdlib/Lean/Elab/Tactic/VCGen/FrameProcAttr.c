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
lean_object* lean_mk_array(lean_object*, lean_object*);
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
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_box(0);
v___x_157_ = lean_unsigned_to_nat(16u);
v___x_158_ = lean_mk_array(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_162_; lean_object* v___f_163_; 
v___x_162_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___f_163_ = lean_alloc_closure((void*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__5_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_163_, 0, v___x_162_);
return v___f_163_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_164_; lean_object* v___f_165_; lean_object* v___f_166_; lean_object* v___f_167_; lean_object* v___f_168_; lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___f_164_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_165_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_166_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_167_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_168_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___f_169_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__9_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___x_170_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_));
v___x_171_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___f_169_);
lean_ctor_set(v___x_171_, 2, v___f_168_);
lean_ctor_set(v___x_171_, 3, v___f_167_);
lean_ctor_set(v___x_171_, 4, v___f_166_);
lean_ctor_set(v___x_171_, 5, v___f_165_);
lean_ctor_set(v___x_171_, 6, v___f_164_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__10_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_);
v___x_174_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2____boxed(lean_object* v_a_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1134118175____hygCtx___hyg_2_();
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg___lam__0(lean_object* v___x_177_, lean_object* v_toPure_178_, lean_object* v_____do__lift_179_){
_start:
{
lean_object* v___x_180_; lean_object* v_ext_181_; lean_object* v_toEnvExtension_182_; lean_object* v_asyncMode_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_180_ = l_Lean_Elab_Tactic_VCGen_frameProcExt;
v_ext_181_ = lean_ctor_get(v___x_180_, 1);
v_toEnvExtension_182_ = lean_ctor_get(v_ext_181_, 0);
v_asyncMode_183_ = lean_ctor_get(v_toEnvExtension_182_, 2);
v___x_184_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_177_, v___x_180_, v_____do__lift_179_, v_asyncMode_183_);
v___x_185_ = lean_apply_2(v_toPure_178_, lean_box(0), v___x_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg___lam__0___boxed(lean_object* v___x_186_, lean_object* v_toPure_187_, lean_object* v_____do__lift_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg___lam__0(v___x_186_, v_toPure_187_, v_____do__lift_188_);
lean_dec_ref(v___x_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg(lean_object* v_inst_190_, lean_object* v_inst_191_){
_start:
{
lean_object* v_toApplicative_192_; lean_object* v_toBind_193_; lean_object* v_getEnv_194_; lean_object* v_toPure_195_; lean_object* v___x_196_; lean_object* v___f_197_; lean_object* v___x_198_; 
v_toApplicative_192_ = lean_ctor_get(v_inst_190_, 0);
lean_inc_ref(v_toApplicative_192_);
v_toBind_193_ = lean_ctor_get(v_inst_190_, 1);
lean_inc(v_toBind_193_);
lean_dec_ref(v_inst_190_);
v_getEnv_194_ = lean_ctor_get(v_inst_191_, 0);
lean_inc(v_getEnv_194_);
lean_dec_ref(v_inst_191_);
v_toPure_195_ = lean_ctor_get(v_toApplicative_192_, 1);
lean_inc(v_toPure_195_);
lean_dec_ref(v_toApplicative_192_);
v___x_196_ = l_Lean_Elab_Tactic_VCGen_instInhabitedFrameProcs;
v___f_197_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_197_, 0, v___x_196_);
lean_closure_set(v___f_197_, 1, v_toPure_195_);
v___x_198_ = lean_apply_4(v_toBind_193_, lean_box(0), lean_box(0), v_getEnv_194_, v___f_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_getFrameProcs(lean_object* v_m_199_, lean_object* v_inst_200_, lean_object* v_inst_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Elab_Tactic_VCGen_getFrameProcs___redArg(v_inst_200_, v_inst_201_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_203_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__0);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__1);
v___x_207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg(lean_object* v_ext_208_, lean_object* v_b_209_, uint8_t v_kind_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_currNamespace_214_; lean_object* v___x_215_; lean_object* v_env_216_; lean_object* v_nextMacroScope_217_; lean_object* v_ngen_218_; lean_object* v_auxDeclNGen_219_; lean_object* v_traceState_220_; lean_object* v_messages_221_; lean_object* v_infoState_222_; lean_object* v_snapshotTasks_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_235_; 
v_currNamespace_214_ = lean_ctor_get(v___y_211_, 6);
v___x_215_ = lean_st_ref_take(v___y_212_);
v_env_216_ = lean_ctor_get(v___x_215_, 0);
v_nextMacroScope_217_ = lean_ctor_get(v___x_215_, 1);
v_ngen_218_ = lean_ctor_get(v___x_215_, 2);
v_auxDeclNGen_219_ = lean_ctor_get(v___x_215_, 3);
v_traceState_220_ = lean_ctor_get(v___x_215_, 4);
v_messages_221_ = lean_ctor_get(v___x_215_, 6);
v_infoState_222_ = lean_ctor_get(v___x_215_, 7);
v_snapshotTasks_223_ = lean_ctor_get(v___x_215_, 8);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_235_ == 0)
{
lean_object* v_unused_236_; 
v_unused_236_ = lean_ctor_get(v___x_215_, 5);
lean_dec(v_unused_236_);
v___x_225_ = v___x_215_;
v_isShared_226_ = v_isSharedCheck_235_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_snapshotTasks_223_);
lean_inc(v_infoState_222_);
lean_inc(v_messages_221_);
lean_inc(v_traceState_220_);
lean_inc(v_auxDeclNGen_219_);
lean_inc(v_ngen_218_);
lean_inc(v_nextMacroScope_217_);
lean_inc(v_env_216_);
lean_dec(v___x_215_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_235_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_230_; 
lean_inc(v_currNamespace_214_);
v___x_227_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_216_, v_ext_208_, v_b_209_, v_kind_210_, v_currNamespace_214_);
v___x_228_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___closed__2);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 5, v___x_228_);
lean_ctor_set(v___x_225_, 0, v___x_227_);
v___x_230_ = v___x_225_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v_nextMacroScope_217_);
lean_ctor_set(v_reuseFailAlloc_234_, 2, v_ngen_218_);
lean_ctor_set(v_reuseFailAlloc_234_, 3, v_auxDeclNGen_219_);
lean_ctor_set(v_reuseFailAlloc_234_, 4, v_traceState_220_);
lean_ctor_set(v_reuseFailAlloc_234_, 5, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_234_, 6, v_messages_221_);
lean_ctor_set(v_reuseFailAlloc_234_, 7, v_infoState_222_);
lean_ctor_set(v_reuseFailAlloc_234_, 8, v_snapshotTasks_223_);
v___x_230_ = v_reuseFailAlloc_234_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = lean_st_ref_put(v___y_212_, v___x_230_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg___boxed(lean_object* v_ext_237_, lean_object* v_b_238_, lean_object* v_kind_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
uint8_t v_kind_boxed_243_; lean_object* v_res_244_; 
v_kind_boxed_243_ = lean_unbox(v_kind_239_);
v_res_244_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg(v_ext_237_, v_b_238_, v_kind_boxed_243_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0(lean_object* v_00_u03b1_245_, lean_object* v_00_u03b2_246_, lean_object* v_00_u03c3_247_, lean_object* v_ext_248_, lean_object* v_b_249_, uint8_t v_kind_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg(v_ext_248_, v_b_249_, v_kind_250_, v___y_251_, v___y_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___boxed(lean_object* v_00_u03b1_255_, lean_object* v_00_u03b2_256_, lean_object* v_00_u03c3_257_, lean_object* v_ext_258_, lean_object* v_b_259_, lean_object* v_kind_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
uint8_t v_kind_boxed_264_; lean_object* v_res_265_; 
v_kind_boxed_264_ = lean_unbox(v_kind_260_);
v_res_265_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0(v_00_u03b1_255_, v_00_u03b2_256_, v_00_u03c3_257_, v_ext_258_, v_b_259_, v_kind_boxed_264_, v___y_261_, v___y_262_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_addFrameProcAttr(lean_object* v_declName_269_, uint8_t v_kind_270_, lean_object* v_a_271_, lean_object* v_a_272_){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___closed__1));
lean_inc(v_declName_269_);
v___x_275_ = l_Lean_ensureAttrDeclIsMeta(v___x_274_, v_declName_269_, v_kind_270_, v_a_271_, v_a_272_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_303_; 
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_303_ == 0)
{
lean_object* v_unused_304_; 
v_unused_304_ = lean_ctor_get(v___x_275_, 0);
lean_dec(v_unused_304_);
v___x_277_ = v___x_275_;
v_isShared_278_ = v_isSharedCheck_303_;
goto v_resetjp_276_;
}
else
{
lean_dec(v___x_275_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_303_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v_env_280_; lean_object* v_options_281_; lean_object* v_ref_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_279_ = lean_st_ref_get(v_a_272_);
v_env_280_ = lean_ctor_get(v___x_279_, 0);
lean_inc_ref(v_env_280_);
lean_dec(v___x_279_);
v_options_281_ = lean_ctor_get(v_a_271_, 2);
v_ref_282_ = lean_ctor_get(v_a_271_, 5);
lean_inc_ref(v_options_281_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v_env_280_);
lean_ctor_set(v___x_283_, 1, v_options_281_);
lean_inc(v_declName_269_);
v___x_284_ = l_Lean_Elab_Tactic_VCGen_getFrameProcFromDeclImpl(v_declName_269_, v___x_283_);
lean_dec_ref_known(v___x_283_, 2);
if (lean_obj_tag(v___x_284_) == 0)
{
lean_object* v_a_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
lean_del_object(v___x_277_);
v_a_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_a_285_);
lean_dec_ref_known(v___x_284_, 1);
v___x_286_ = l_Lean_Elab_Tactic_VCGen_frameProcExt;
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v_declName_269_);
lean_ctor_set(v___x_287_, 1, v_a_285_);
v___x_288_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Elab_Tactic_VCGen_addFrameProcAttr_spec__0___redArg(v___x_286_, v___x_287_, v_kind_270_, v_a_271_, v_a_272_);
return v___x_288_;
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_302_; 
lean_dec(v_declName_269_);
v_a_289_ = lean_ctor_get(v___x_284_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v___x_284_);
if (v_isSharedCheck_302_ == 0)
{
v___x_291_ = v___x_284_;
v_isShared_292_ = v_isSharedCheck_302_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_284_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_302_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_293_ = lean_io_error_to_string(v_a_289_);
if (v_isShared_278_ == 0)
{
lean_ctor_set_tag(v___x_277_, 3);
lean_ctor_set(v___x_277_, 0, v___x_293_);
v___x_295_ = v___x_277_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_301_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_299_; 
v___x_296_ = l_Lean_MessageData_ofFormat(v___x_295_);
lean_inc(v_ref_282_);
v___x_297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_297_, 0, v_ref_282_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___x_297_);
v___x_299_ = v___x_291_;
goto v_reusejp_298_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_297_);
v___x_299_ = v_reuseFailAlloc_300_;
goto v_reusejp_298_;
}
v_reusejp_298_:
{
return v___x_299_;
}
}
}
}
}
}
else
{
lean_dec(v_declName_269_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_addFrameProcAttr___boxed(lean_object* v_declName_305_, lean_object* v_kind_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
uint8_t v_kind_boxed_310_; lean_object* v_res_311_; 
v_kind_boxed_310_ = lean_unbox(v_kind_306_);
v_res_311_ = l_Lean_Elab_Tactic_VCGen_addFrameProcAttr(v_declName_305_, v_kind_boxed_310_, v_a_307_, v_a_308_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(lean_object* v_declName_312_, lean_object* v___stx_313_, uint8_t v_kind_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Elab_Tactic_VCGen_addFrameProcAttr(v_declName_312_, v_kind_314_, v___y_315_, v___y_316_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object* v_declName_319_, lean_object* v___stx_320_, lean_object* v_kind_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
uint8_t v_kind_boxed_325_; lean_object* v_res_326_; 
v_kind_boxed_325_ = lean_unbox(v_kind_321_);
v_res_326_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(v_declName_319_, v___stx_320_, v_kind_boxed_325_, v___y_322_, v___y_323_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___stx_320_);
return v_res_326_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_327_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_328_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__0);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_330_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
lean_ctor_set(v___x_332_, 2, v___x_331_);
lean_ctor_set(v___x_332_, 3, v___x_331_);
lean_ctor_set(v___x_332_, 4, v___x_330_);
lean_ctor_set(v___x_332_, 5, v___x_330_);
lean_ctor_set(v___x_332_, 6, v___x_330_);
lean_ctor_set(v___x_332_, 7, v___x_330_);
lean_ctor_set(v___x_332_, 8, v___x_330_);
lean_ctor_set(v___x_332_, 9, v___x_330_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = lean_unsigned_to_nat(32u);
v___x_334_ = lean_mk_empty_array_with_capacity(v___x_333_);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_336_ = ((size_t)5ULL);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_unsigned_to_nat(32u);
v___x_339_ = lean_mk_empty_array_with_capacity(v___x_338_);
v___x_340_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__3);
v___x_341_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_339_);
lean_ctor_set(v___x_341_, 2, v___x_337_);
lean_ctor_set(v___x_341_, 3, v___x_337_);
lean_ctor_set_usize(v___x_341_, 4, v___x_336_);
return v___x_341_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_342_ = lean_box(1);
v___x_343_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__4);
v___x_344_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__1);
v___x_345_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
lean_ctor_set(v___x_345_, 2, v___x_342_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_msgData_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; lean_object* v_env_351_; lean_object* v_options_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_350_ = lean_st_ref_get(v___y_348_);
v_env_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc_ref(v_env_351_);
lean_dec(v___x_350_);
v_options_352_ = lean_ctor_get(v___y_347_, 2);
v___x_353_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__2);
v___x_354_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___closed__5);
lean_inc_ref(v_options_352_);
v___x_355_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_355_, 0, v_env_351_);
lean_ctor_set(v___x_355_, 1, v___x_353_);
lean_ctor_set(v___x_355_, 2, v___x_354_);
lean_ctor_set(v___x_355_, 3, v_options_352_);
v___x_356_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v_msgData_346_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_msgData_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0(v_msgData_358_, v___y_359_, v___y_360_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(lean_object* v_msg_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_ref_367_; lean_object* v___x_368_; lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_377_; 
v_ref_367_ = lean_ctor_get(v___y_364_, 5);
v___x_368_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0_spec__0(v_msg_363_, v___y_364_, v___y_365_);
v_a_369_ = lean_ctor_get(v___x_368_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_368_);
if (v_isSharedCheck_377_ == 0)
{
v___x_371_ = v___x_368_;
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_368_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_377_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_375_; 
lean_inc(v_ref_367_);
v___x_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_373_, 0, v_ref_367_);
lean_ctor_set(v___x_373_, 1, v_a_369_);
if (v_isShared_372_ == 0)
{
lean_ctor_set_tag(v___x_371_, 1);
lean_ctor_set(v___x_371_, 0, v___x_373_);
v___x_375_ = v___x_371_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_msg_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(v_msg_378_, v___y_379_, v___y_380_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_382_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_));
v___x_385_ = l_Lean_stringToMessageData(v___x_384_);
return v___x_385_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__2_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_));
v___x_388_ = l_Lean_stringToMessageData(v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(lean_object* v___x_389_, lean_object* v_decl_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_394_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_);
v___x_395_ = l_Lean_MessageData_ofName(v___x_389_);
v___x_396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_394_);
lean_ctor_set(v___x_396_, 1, v___x_395_);
v___x_397_ = lean_obj_once(&l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1___closed__3_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(v___x_398_, v___y_391_, v___y_392_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object* v___x_400_, lean_object* v_decl_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___lam__1_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(v___x_400_, v_decl_401_, v___y_402_, v___y_403_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v_decl_401_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__32_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_));
v___x_493_ = l_Lean_registerBuiltinAttribute(v___x_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2____boxed(lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l___private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2_();
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_496_, lean_object* v_msg_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___redArg(v_msg_497_, v___y_498_, v___y_499_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_502_, lean_object* v_msg_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_VCGen_FrameProcAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_FrameProcAttr_1192303900____hygCtx___hyg_2__spec__0(v_00_u03b1_502_, v_msg_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
return v_res_507_;
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
