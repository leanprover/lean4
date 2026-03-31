// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Attr
// Imports: public import Lean.Elab.Tactic.Simp public import Std.Tactic.BVDecide.Syntax
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
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Simp_registerSimprocAttr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* l_Lean_Name_mkStr7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(lean_object*, lean_object*, uint8_t, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sat"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 199, 37, 233, 64, 174, 173, 134)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "BVDecide"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__12_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(8, 168, 14, 82, 188, 236, 147, 179)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__12_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__12_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Frontend"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__14_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__12_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(241, 77, 173, 50, 9, 24, 54, 150)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__14_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__14_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__15_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__15_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__15_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__16_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__14_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__15_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 61, 132, 134, 92, 229, 233, 240)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__16_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__16_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__17_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__16_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(36, 110, 67, 26, 14, 230, 237, 24)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__17_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__17_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__18_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__17_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 59, 58, 26, 252, 129, 241, 190)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__18_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__18_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__19_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__18_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 251, 73, 58, 48, 5, 178, 145)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__19_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__19_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__20_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__19_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(226, 45, 120, 6, 149, 92, 82, 118)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__20_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__20_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__21_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__20_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(59, 100, 1, 28, 14, 168, 229, 227)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__21_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__21_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__22_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__21_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(54, 90, 154, 245, 99, 63, 152, 216)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__22_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__22_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__23_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__23_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__23_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__24_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__22_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__23_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(155, 159, 253, 92, 146, 69, 2, 229)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__24_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__24_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__25_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__25_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__25_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__26_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__24_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__25_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 209, 15, 222, 36, 133, 231, 122)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__26_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__26_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__27_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__26_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(199, 144, 145, 193, 241, 173, 88, 141)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__27_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__27_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__28_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__27_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(73, 6, 184, 147, 13, 84, 64, 43)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__28_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__28_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__29_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__28_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(32, 249, 59, 75, 64, 203, 31, 45)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__29_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__29_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__30_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__29_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(209, 15, 200, 94, 39, 211, 82, 122)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__30_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__30_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__31_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__30_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(68, 54, 76, 24, 63, 126, 31, 154)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__31_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__31_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__32_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__31_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__15_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(168, 25, 212, 149, 63, 123, 50, 60)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__32_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__32_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__33_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__32_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(921759773) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(14, 243, 17, 184, 17, 126, 248, 24)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__33_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__33_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__34_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__34_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__34_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__35_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__33_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__34_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(89, 135, 235, 141, 78, 202, 134, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__35_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__35_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__36_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__36_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__36_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__37_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__35_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__36_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(145, 90, 52, 184, 106, 21, 216, 45)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__37_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__37_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__38_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__37_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(108, 139, 203, 35, 161, 91, 82, 86)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__38_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__38_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2____boxed(lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "bv"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(139, 41, 106, 94, 234, 34, 111, 146)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "solver"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(187, 159, 50, 22, 96, 145, 4, 16)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(72, 158, 105, 178, 36, 68, 6, 203)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 500, .m_capacity = 500, .m_length = 499, .m_data = "Name of the SAT solver used by Lean.Elab.Tactic.BVDecide tactics.\n\n     1. If this is set to something besides the empty string they will use that binary.\n\n     2. If this is set to the empty string they will check if there is a cadical binary next to theexecuting program. Usually that program is going to be `lean` itself and we do ship a`cadical` next to it.\n\n     3. If that does not succeed try to call `cadical` from PATH. The empty string default indicatesto use the one that ships with Lean."};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_5 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(109, 157, 42, 75, 34, 202, 38, 95)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value_aux_5),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(214, 182, 7, 175, 119, 199, 66, 237)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_sat_solver;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "BVDecideConfig"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3__value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3__value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(224, 9, 34, 142, 214, 235, 14, 251)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__14_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__17_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__18;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__19_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__20;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__21_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__22 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__22_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__23 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__23_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__24 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__24_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__9___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Error evaluating configuration\n"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "\n\nException: "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Configuration contains `sorry`"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "Error evaluating configuration: Environment does not yet contain type "};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__9;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 16, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(10) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bv_normalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(107, 250, 93, 18, 255, 117, 252, 211)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "simp theorems used by bv_normalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "bvNormalizeExt"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(14, 26, 101, 129, 96, 146, 148, 11)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeExt;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "int_toBitVec"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(86, 82, 181, 235, 29, 69, 188, 18)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "simp theorems used to convert UIntX/IntX statements into BitVec ones"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "intToBitVecExt"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(254, 200, 236, 49, 216, 88, 223, 50)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_intToBitVecExt;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "bv_normalize_proc"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(129, 55, 180, 228, 60, 0, 67, 150)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "simprocs used by bv_normalize"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_;
static const lean_string_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "bvNormalizeSimprocExt"};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(188, 95, 32, 5, 74, 186, 96, 166)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(205, 232, 230, 43, 194, 2, 193, 237)}};
static const lean_ctor_object l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value_aux_4),((lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(43, 161, 84, 53, 66, 95, 10, 16)}};
static const lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeSimprocExt;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declare"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__0_value),LEAN_SCALAR_PTR_LITERAL(12, 217, 76, 92, 115, 157, 174, 191)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__3_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__4_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__6_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__2_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__6_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__7 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__7_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "unexpected type at bv_normalize simproc"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__9 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__9_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__11 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__11_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Simproc"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__12 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__12_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Sum"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__13 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__13_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inl"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__14 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__14_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__13_value),LEAN_SCALAR_PTR_LITERAL(249, 106, 118, 161, 227, 189, 67, 81)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__15_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__14_value),LEAN_SCALAR_PTR_LITERAL(236, 33, 85, 75, 207, 191, 2, 96)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__15 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__15_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__11_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__12_value),LEAN_SCALAR_PTR_LITERAL(18, 160, 179, 254, 130, 82, 156, 255)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DSimproc"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__22 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__22_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__11_value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__22_value),LEAN_SCALAR_PTR_LITERAL(119, 227, 62, 233, 71, 149, 243, 160)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23_value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__25 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__25_value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__26 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__26_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__25_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__26_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27 = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "Not implemented yet, [-builtin_bv_normalize_proc]"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "addBVNormalizeProcBuiltinAttr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed, .m_arity = 11, .m_num_fixed = 5, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__11_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__13_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__32_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1596612692) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(73, 50, 70, 134, 5, 67, 42, 139)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__34_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(218, 90, 82, 225, 212, 148, 134, 97)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__36_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 7, 177, 203, 127, 7, 203, 6)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(231, 134, 121, 139, 58, 106, 105, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "bvNormalizeProcBuiltinAttr"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 5, 36, 101, 149, 10, 160, 102)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Builtin bv_normalize simproc"};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__7_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__8_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__9_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_94_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_95_ = 0;
v___x_96_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__38_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_97_ = l_Lean_registerTraceClass(v___x_94_, v___x_95_, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2____boxed(lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_();
return v_res_99_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_unsigned_to_nat(3575118154u);
v___x_106_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__32_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_107_ = l_Lean_Name_num___override(v___x_106_, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__34_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_109_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_);
v___x_110_ = l_Lean_Name_str___override(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__36_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_112_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_);
v___x_113_ = l_Lean_Name_str___override(v___x_112_, v___x_111_);
return v___x_113_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_114_ = lean_unsigned_to_nat(2u);
v___x_115_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_);
v___x_116_ = l_Lean_Name_num___override(v___x_115_, v___x_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_118_; uint8_t v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_118_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_));
v___x_119_ = 0;
v___x_120_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_);
v___x_121_ = l_Lean_registerTraceClass(v___x_118_, v___x_119_, v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2____boxed(lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_();
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__spec__0(lean_object* v_name_124_, lean_object* v_decl_125_, lean_object* v_ref_126_){
_start:
{
lean_object* v_defValue_128_; lean_object* v_descr_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_155_; 
v_defValue_128_ = lean_ctor_get(v_decl_125_, 0);
v_descr_129_ = lean_ctor_get(v_decl_125_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_decl_125_);
if (v_isSharedCheck_155_ == 0)
{
v___x_131_ = v_decl_125_;
v_isShared_132_ = v_isSharedCheck_155_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_descr_129_);
lean_inc(v_defValue_128_);
lean_dec(v_decl_125_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_155_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
lean_inc(v_defValue_128_);
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v_defValue_128_);
lean_inc_n(v_name_124_, 2);
v___x_134_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_134_, 0, v_name_124_);
lean_ctor_set(v___x_134_, 1, v_ref_126_);
lean_ctor_set(v___x_134_, 2, v___x_133_);
lean_ctor_set(v___x_134_, 3, v_descr_129_);
v___x_135_ = lean_register_option(v_name_124_, v___x_134_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_145_; 
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_145_ == 0)
{
lean_object* v_unused_146_; 
v_unused_146_ = lean_ctor_get(v___x_135_, 0);
lean_dec(v_unused_146_);
v___x_137_ = v___x_135_;
v_isShared_138_ = v_isSharedCheck_145_;
goto v_resetjp_136_;
}
else
{
lean_dec(v___x_135_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_145_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v_defValue_128_);
lean_ctor_set(v___x_131_, 0, v_name_124_);
v___x_140_ = v___x_131_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_name_124_);
lean_ctor_set(v_reuseFailAlloc_144_, 1, v_defValue_128_);
v___x_140_ = v_reuseFailAlloc_144_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_142_; 
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_140_);
v___x_142_ = v___x_137_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v___x_140_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
else
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_154_; 
lean_del_object(v___x_131_);
lean_dec(v_defValue_128_);
lean_dec(v_name_124_);
v_a_147_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_154_ == 0)
{
v___x_149_ = v___x_135_;
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_135_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_154_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_152_; 
if (v_isShared_150_ == 0)
{
v___x_152_ = v___x_149_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v_a_147_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_156_, lean_object* v_decl_157_, lean_object* v_ref_158_, lean_object* v_a_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lean_Option_register___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__spec__0(v_name_156_, v_decl_157_, v_ref_158_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_179_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_));
v___x_180_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_));
v___x_181_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_));
v___x_182_ = l_Lean_Option_register___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4__spec__0(v___x_179_, v___x_180_, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4____boxed(lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_();
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_(lean_object* v_e_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; uint8_t v___x_201_; lean_object* v___x_202_; 
v___x_199_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_));
v___x_200_ = 0;
v___x_201_ = 1;
v___x_202_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_199_, v_e_193_, v___x_200_, v___x_201_, v_a_194_, v_a_195_, v_a_196_, v_a_197_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3____boxed(lean_object* v_e_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_(v_e_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_(lean_object* v_e_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_(v_e_210_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3____boxed(lean_object* v_e_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_(v_e_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__5___redArg(lean_object* v_a_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
lean_object* v___x_230_; 
v___x_230_ = lean_box(0);
return v___x_230_;
}
else
{
lean_object* v_key_231_; lean_object* v_value_232_; lean_object* v_tail_233_; uint8_t v___x_234_; 
v_key_231_ = lean_ctor_get(v_x_229_, 0);
v_value_232_ = lean_ctor_get(v_x_229_, 1);
v_tail_233_ = lean_ctor_get(v_x_229_, 2);
v___x_234_ = lean_name_eq(v_key_231_, v_a_228_);
if (v___x_234_ == 0)
{
v_x_229_ = v_tail_233_;
goto _start;
}
else
{
lean_object* v___x_236_; 
lean_inc(v_value_232_);
v___x_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_236_, 0, v_value_232_);
return v___x_236_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_237_, lean_object* v_x_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__5___redArg(v_a_237_, v_x_238_);
lean_dec(v_x_238_);
lean_dec(v_a_237_);
return v_res_239_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_240_; uint64_t v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(1723u);
v___x_241_ = lean_uint64_of_nat(v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg(lean_object* v_m_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_buckets_244_; lean_object* v___x_245_; uint64_t v___y_247_; 
v_buckets_244_ = lean_ctor_get(v_m_242_, 1);
v___x_245_ = lean_array_get_size(v_buckets_244_);
if (lean_obj_tag(v_a_243_) == 0)
{
uint64_t v___x_261_; 
v___x_261_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg___closed__0);
v___y_247_ = v___x_261_;
goto v___jp_246_;
}
else
{
uint64_t v_hash_262_; 
v_hash_262_ = lean_ctor_get_uint64(v_a_243_, sizeof(void*)*2);
v___y_247_ = v_hash_262_;
goto v___jp_246_;
}
v___jp_246_:
{
uint64_t v___x_248_; uint64_t v___x_249_; uint64_t v_fold_250_; uint64_t v___x_251_; uint64_t v___x_252_; uint64_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; size_t v___x_257_; size_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_248_ = 32ULL;
v___x_249_ = lean_uint64_shift_right(v___y_247_, v___x_248_);
v_fold_250_ = lean_uint64_xor(v___y_247_, v___x_249_);
v___x_251_ = 16ULL;
v___x_252_ = lean_uint64_shift_right(v_fold_250_, v___x_251_);
v___x_253_ = lean_uint64_xor(v_fold_250_, v___x_252_);
v___x_254_ = lean_uint64_to_usize(v___x_253_);
v___x_255_ = lean_usize_of_nat(v___x_245_);
v___x_256_ = ((size_t)1ULL);
v___x_257_ = lean_usize_sub(v___x_255_, v___x_256_);
v___x_258_ = lean_usize_land(v___x_254_, v___x_257_);
v___x_259_ = lean_array_uget_borrowed(v_buckets_244_, v___x_258_);
v___x_260_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__5___redArg(v_a_243_, v___x_259_);
return v___x_260_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg___boxed(lean_object* v_m_263_, lean_object* v_a_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg(v_m_263_, v_a_264_);
lean_dec(v_a_264_);
lean_dec_ref(v_m_263_);
return v_res_265_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__9___redArg(lean_object* v_keys_266_, lean_object* v_i_267_, lean_object* v_k_268_){
_start:
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = lean_array_get_size(v_keys_266_);
v___x_270_ = lean_nat_dec_lt(v_i_267_, v___x_269_);
if (v___x_270_ == 0)
{
lean_dec(v_i_267_);
return v___x_270_;
}
else
{
lean_object* v_k_x27_271_; uint8_t v___x_272_; 
v_k_x27_271_ = lean_array_fget_borrowed(v_keys_266_, v_i_267_);
v___x_272_ = l_Lean_instBEqExtraModUse_beq(v_k_268_, v_k_x27_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(1u);
v___x_274_ = lean_nat_add(v_i_267_, v___x_273_);
lean_dec(v_i_267_);
v_i_267_ = v___x_274_;
goto _start;
}
else
{
lean_dec(v_i_267_);
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__9___redArg___boxed(lean_object* v_keys_276_, lean_object* v_i_277_, lean_object* v_k_278_){
_start:
{
uint8_t v_res_279_; lean_object* v_r_280_; 
v_res_279_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__9___redArg(v_keys_276_, v_i_277_, v_k_278_);
lean_dec_ref(v_k_278_);
lean_dec_ref(v_keys_276_);
v_r_280_ = lean_box(v_res_279_);
return v_r_280_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_281_; size_t v___x_282_; size_t v___x_283_; 
v___x_281_ = ((size_t)5ULL);
v___x_282_ = ((size_t)1ULL);
v___x_283_ = lean_usize_shift_left(v___x_282_, v___x_281_);
return v___x_283_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_284_; size_t v___x_285_; size_t v___x_286_; 
v___x_284_ = ((size_t)1ULL);
v___x_285_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
v___x_286_ = lean_usize_sub(v___x_285_, v___x_284_);
return v___x_286_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_287_, size_t v_x_288_, lean_object* v_x_289_){
_start:
{
if (lean_obj_tag(v_x_287_) == 0)
{
lean_object* v_es_290_; lean_object* v___x_291_; size_t v___x_292_; size_t v___x_293_; size_t v___x_294_; lean_object* v_j_295_; lean_object* v___x_296_; 
v_es_290_ = lean_ctor_get(v_x_287_, 0);
v___x_291_ = lean_box(2);
v___x_292_ = ((size_t)5ULL);
v___x_293_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_294_ = lean_usize_land(v_x_288_, v___x_293_);
v_j_295_ = lean_usize_to_nat(v___x_294_);
v___x_296_ = lean_array_get_borrowed(v___x_291_, v_es_290_, v_j_295_);
lean_dec(v_j_295_);
switch(lean_obj_tag(v___x_296_))
{
case 0:
{
lean_object* v_key_297_; uint8_t v___x_298_; 
v_key_297_ = lean_ctor_get(v___x_296_, 0);
v___x_298_ = l_Lean_instBEqExtraModUse_beq(v_x_289_, v_key_297_);
return v___x_298_;
}
case 1:
{
lean_object* v_node_299_; size_t v___x_300_; 
v_node_299_ = lean_ctor_get(v___x_296_, 0);
v___x_300_ = lean_usize_shift_right(v_x_288_, v___x_292_);
v_x_287_ = v_node_299_;
v_x_288_ = v___x_300_;
goto _start;
}
default: 
{
uint8_t v___x_302_; 
v___x_302_ = 0;
return v___x_302_;
}
}
}
else
{
lean_object* v_ks_303_; lean_object* v___x_304_; uint8_t v___x_305_; 
v_ks_303_ = lean_ctor_get(v_x_287_, 0);
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__9___redArg(v_ks_303_, v___x_304_, v_x_289_);
return v___x_305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_){
_start:
{
size_t v_x_12384__boxed_309_; uint8_t v_res_310_; lean_object* v_r_311_; 
v_x_12384__boxed_309_ = lean_unbox_usize(v_x_307_);
lean_dec(v_x_307_);
v_res_310_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg(v_x_306_, v_x_12384__boxed_309_, v_x_308_);
lean_dec_ref(v_x_308_);
lean_dec_ref(v_x_306_);
v_r_311_ = lean_box(v_res_310_);
return v_r_311_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_x_312_, lean_object* v_x_313_){
_start:
{
uint64_t v___x_314_; size_t v___x_315_; uint8_t v___x_316_; 
v___x_314_ = l_Lean_instHashableExtraModUse_hash(v_x_313_);
v___x_315_ = lean_uint64_to_usize(v___x_314_);
v___x_316_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg(v_x_312_, v___x_315_, v_x_313_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___redArg(v_x_317_, v_x_318_);
lean_dec_ref(v_x_318_);
lean_dec_ref(v_x_317_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__4(lean_object* v_msgData_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; lean_object* v_env_328_; lean_object* v___x_329_; lean_object* v_mctx_330_; lean_object* v_lctx_331_; lean_object* v_options_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_327_ = lean_st_ref_get(v___y_325_);
v_env_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc_ref(v_env_328_);
lean_dec(v___x_327_);
v___x_329_ = lean_st_ref_get(v___y_323_);
v_mctx_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_mctx_330_);
lean_dec(v___x_329_);
v_lctx_331_ = lean_ctor_get(v___y_322_, 2);
v_options_332_ = lean_ctor_get(v___y_324_, 2);
lean_inc_ref(v_options_332_);
lean_inc_ref(v_lctx_331_);
v___x_333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_333_, 0, v_env_328_);
lean_ctor_set(v___x_333_, 1, v_mctx_330_);
lean_ctor_set(v___x_333_, 2, v_lctx_331_);
lean_ctor_set(v___x_333_, 3, v_options_332_);
v___x_334_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v_msgData_321_);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__4___boxed(lean_object* v_msgData_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__4(v_msgData_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_342_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_343_; double v___x_344_; 
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_float_of_nat(v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_347_, lean_object* v_msg_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_ref_354_; lean_object* v___x_355_; lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_400_; 
v_ref_354_ = lean_ctor_get(v___y_351_, 5);
v___x_355_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__4(v_msg_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_400_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_400_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_400_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; lean_object* v_traceState_361_; lean_object* v_env_362_; lean_object* v_nextMacroScope_363_; lean_object* v_ngen_364_; lean_object* v_auxDeclNGen_365_; lean_object* v_cache_366_; lean_object* v_messages_367_; lean_object* v_infoState_368_; lean_object* v_snapshotTasks_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_399_; 
v___x_360_ = lean_st_ref_take(v___y_352_);
v_traceState_361_ = lean_ctor_get(v___x_360_, 4);
v_env_362_ = lean_ctor_get(v___x_360_, 0);
v_nextMacroScope_363_ = lean_ctor_get(v___x_360_, 1);
v_ngen_364_ = lean_ctor_get(v___x_360_, 2);
v_auxDeclNGen_365_ = lean_ctor_get(v___x_360_, 3);
v_cache_366_ = lean_ctor_get(v___x_360_, 5);
v_messages_367_ = lean_ctor_get(v___x_360_, 6);
v_infoState_368_ = lean_ctor_get(v___x_360_, 7);
v_snapshotTasks_369_ = lean_ctor_get(v___x_360_, 8);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_399_ == 0)
{
v___x_371_ = v___x_360_;
v_isShared_372_ = v_isSharedCheck_399_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_snapshotTasks_369_);
lean_inc(v_infoState_368_);
lean_inc(v_messages_367_);
lean_inc(v_cache_366_);
lean_inc(v_traceState_361_);
lean_inc(v_auxDeclNGen_365_);
lean_inc(v_ngen_364_);
lean_inc(v_nextMacroScope_363_);
lean_inc(v_env_362_);
lean_dec(v___x_360_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_399_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
uint64_t v_tid_373_; lean_object* v_traces_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_398_; 
v_tid_373_ = lean_ctor_get_uint64(v_traceState_361_, sizeof(void*)*1);
v_traces_374_ = lean_ctor_get(v_traceState_361_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v_traceState_361_);
if (v_isSharedCheck_398_ == 0)
{
v___x_376_ = v_traceState_361_;
v_isShared_377_ = v_isSharedCheck_398_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_traces_374_);
lean_dec(v_traceState_361_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_398_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_378_; double v___x_379_; uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v___x_378_ = lean_box(0);
v___x_379_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_380_ = 0;
v___x_381_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_));
v___x_382_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_382_, 0, v_cls_347_);
lean_ctor_set(v___x_382_, 1, v___x_378_);
lean_ctor_set(v___x_382_, 2, v___x_381_);
lean_ctor_set_float(v___x_382_, sizeof(void*)*3, v___x_379_);
lean_ctor_set_float(v___x_382_, sizeof(void*)*3 + 8, v___x_379_);
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*3 + 16, v___x_380_);
v___x_383_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_384_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v_a_356_);
lean_ctor_set(v___x_384_, 2, v___x_383_);
lean_inc(v_ref_354_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_ref_354_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = l_Lean_PersistentArray_push___redArg(v_traces_374_, v___x_385_);
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v___x_386_);
v___x_388_ = v___x_376_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_386_);
lean_ctor_set_uint64(v_reuseFailAlloc_397_, sizeof(void*)*1, v_tid_373_);
v___x_388_ = v_reuseFailAlloc_397_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_390_; 
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 4, v___x_388_);
v___x_390_ = v___x_371_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_env_362_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_nextMacroScope_363_);
lean_ctor_set(v_reuseFailAlloc_396_, 2, v_ngen_364_);
lean_ctor_set(v_reuseFailAlloc_396_, 3, v_auxDeclNGen_365_);
lean_ctor_set(v_reuseFailAlloc_396_, 4, v___x_388_);
lean_ctor_set(v_reuseFailAlloc_396_, 5, v_cache_366_);
lean_ctor_set(v_reuseFailAlloc_396_, 6, v_messages_367_);
lean_ctor_set(v_reuseFailAlloc_396_, 7, v_infoState_368_);
lean_ctor_set(v_reuseFailAlloc_396_, 8, v_snapshotTasks_369_);
v___x_390_ = v_reuseFailAlloc_396_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_391_ = lean_st_ref_set(v___y_352_, v___x_390_);
v___x_392_ = lean_box(0);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_392_);
v___x_394_ = v___x_358_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_401_, lean_object* v_msg_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg(v_cls_401_, v_msg_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_);
lean_dec(v___y_406_);
lean_dec_ref(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
return v_res_408_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__1));
v___x_412_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__0));
v___x_413_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_412_, v___x_411_);
return v___x_413_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_414_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__3);
v___x_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
return v___x_416_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_417_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
return v___x_418_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4);
v___x_420_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
lean_ctor_set(v___x_420_, 1, v___x_419_);
lean_ctor_set(v___x_420_, 2, v___x_419_);
lean_ctor_set(v___x_420_, 3, v___x_419_);
lean_ctor_set(v___x_420_, 4, v___x_419_);
lean_ctor_set(v___x_420_, 5, v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__9));
v___x_426_ = l_Lean_stringToMessageData(v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__11));
v___x_429_ = l_Lean_stringToMessageData(v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_));
v___x_431_ = l_Lean_stringToMessageData(v___x_430_);
return v___x_431_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v_cls_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_cls_435_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__8));
v___x_436_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__15));
v___x_437_ = l_Lean_Name_append(v___x_436_, v_cls_435_);
return v___x_437_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__18(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__17));
v___x_440_ = l_Lean_stringToMessageData(v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__20(void){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_442_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__19));
v___x_443_ = l_Lean_stringToMessageData(v___x_442_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0(lean_object* v_mod_448_, uint8_t v_isMeta_449_, lean_object* v_hint_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; lean_object* v_env_459_; uint8_t v_isExporting_460_; lean_object* v___x_461_; lean_object* v_env_462_; lean_object* v___x_463_; lean_object* v_entry_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_458_ = lean_st_ref_get(v___y_456_);
v_env_459_ = lean_ctor_get(v___x_458_, 0);
lean_inc_ref(v_env_459_);
lean_dec(v___x_458_);
v_isExporting_460_ = lean_ctor_get_uint8(v_env_459_, sizeof(void*)*8);
lean_dec_ref(v_env_459_);
v___x_461_ = lean_st_ref_get(v___y_456_);
v_env_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc_ref(v_env_462_);
lean_dec(v___x_461_);
v___x_463_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__2);
lean_inc(v_mod_448_);
v_entry_464_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_464_, 0, v_mod_448_);
lean_ctor_set_uint8(v_entry_464_, sizeof(void*)*1, v_isExporting_460_);
lean_ctor_set_uint8(v_entry_464_, sizeof(void*)*1 + 1, v_isMeta_449_);
v___x_465_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_466_ = lean_box(1);
v___x_467_ = lean_box(0);
v___x_510_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_463_, v___x_465_, v_env_462_, v___x_466_, v___x_467_);
v___x_511_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___redArg(v___x_510_, v_entry_464_);
lean_dec(v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v_options_512_; uint8_t v_hasTrace_513_; 
v_options_512_ = lean_ctor_get(v___y_455_, 2);
v_hasTrace_513_ = lean_ctor_get_uint8(v_options_512_, sizeof(void*)*1);
if (v_hasTrace_513_ == 0)
{
lean_dec(v_hint_450_);
lean_dec(v_mod_448_);
v___y_469_ = v___y_454_;
v___y_470_ = v___y_456_;
goto v___jp_468_;
}
else
{
lean_object* v_inheritedTraceOptions_514_; lean_object* v_cls_515_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___x_535_; uint8_t v___x_536_; 
v_inheritedTraceOptions_514_ = lean_ctor_get(v___y_455_, 13);
v_cls_515_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__8));
v___x_535_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__16);
v___x_536_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_514_, v_options_512_, v___x_535_);
if (v___x_536_ == 0)
{
lean_dec(v_hint_450_);
lean_dec(v_mod_448_);
v___y_469_ = v___y_454_;
v___y_470_ = v___y_456_;
goto v___jp_468_;
}
else
{
lean_object* v___x_537_; lean_object* v___y_539_; 
v___x_537_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__18, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__18_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__18);
if (v_isExporting_460_ == 0)
{
lean_object* v___x_546_; 
v___x_546_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__23));
v___y_539_ = v___x_546_;
goto v___jp_538_;
}
else
{
lean_object* v___x_547_; 
v___x_547_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__24));
v___y_539_ = v___x_547_;
goto v___jp_538_;
}
v___jp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
lean_inc_ref(v___y_539_);
v___x_540_ = l_Lean_stringToMessageData(v___y_539_);
v___x_541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_537_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
v___x_542_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__20, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__20_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__20);
v___x_543_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_541_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
if (v_isMeta_449_ == 0)
{
lean_object* v___x_544_; 
v___x_544_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__21));
v___y_522_ = v___x_543_;
v___y_523_ = v___x_544_;
goto v___jp_521_;
}
else
{
lean_object* v___x_545_; 
v___x_545_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__22));
v___y_522_ = v___x_543_;
v___y_523_ = v___x_545_;
goto v___jp_521_;
}
}
}
v___jp_516_:
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_519_, 0, v___y_517_);
lean_ctor_set(v___x_519_, 1, v___y_518_);
v___x_520_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg(v_cls_515_, v___x_519_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
if (lean_obj_tag(v___x_520_) == 0)
{
lean_dec_ref(v___x_520_);
v___y_469_ = v___y_454_;
v___y_470_ = v___y_456_;
goto v___jp_468_;
}
else
{
lean_dec_ref(v_entry_464_);
return v___x_520_;
}
}
v___jp_521_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint8_t v___x_530_; 
lean_inc_ref(v___y_523_);
v___x_524_ = l_Lean_stringToMessageData(v___y_523_);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___y_522_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__10);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = l_Lean_MessageData_ofName(v_mod_448_);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = l_Lean_Name_isAnonymous(v_hint_450_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_531_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__12);
v___x_532_ = l_Lean_MessageData_ofName(v_hint_450_);
v___x_533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___y_517_ = v___x_529_;
v___y_518_ = v___x_533_;
goto v___jp_516_;
}
else
{
lean_object* v___x_534_; 
lean_dec(v_hint_450_);
v___x_534_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__13);
v___y_517_ = v___x_529_;
v___y_518_ = v___x_534_;
goto v___jp_516_;
}
}
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec_ref(v_entry_464_);
lean_dec(v_hint_450_);
lean_dec(v_mod_448_);
v___x_548_ = lean_box(0);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
v___jp_468_:
{
lean_object* v___x_471_; lean_object* v_toEnvExtension_472_; lean_object* v_env_473_; lean_object* v_nextMacroScope_474_; lean_object* v_ngen_475_; lean_object* v_auxDeclNGen_476_; lean_object* v_traceState_477_; lean_object* v_messages_478_; lean_object* v_infoState_479_; lean_object* v_snapshotTasks_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_508_; 
v___x_471_ = lean_st_ref_take(v___y_470_);
v_toEnvExtension_472_ = lean_ctor_get(v___x_465_, 0);
v_env_473_ = lean_ctor_get(v___x_471_, 0);
v_nextMacroScope_474_ = lean_ctor_get(v___x_471_, 1);
v_ngen_475_ = lean_ctor_get(v___x_471_, 2);
v_auxDeclNGen_476_ = lean_ctor_get(v___x_471_, 3);
v_traceState_477_ = lean_ctor_get(v___x_471_, 4);
v_messages_478_ = lean_ctor_get(v___x_471_, 6);
v_infoState_479_ = lean_ctor_get(v___x_471_, 7);
v_snapshotTasks_480_ = lean_ctor_get(v___x_471_, 8);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_471_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v___x_471_, 5);
lean_dec(v_unused_509_);
v___x_482_ = v___x_471_;
v_isShared_483_ = v_isSharedCheck_508_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_snapshotTasks_480_);
lean_inc(v_infoState_479_);
lean_inc(v_messages_478_);
lean_inc(v_traceState_477_);
lean_inc(v_auxDeclNGen_476_);
lean_inc(v_ngen_475_);
lean_inc(v_nextMacroScope_474_);
lean_inc(v_env_473_);
lean_dec(v___x_471_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_508_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v_asyncMode_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_488_; 
v_asyncMode_484_ = lean_ctor_get(v_toEnvExtension_472_, 2);
v___x_485_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_465_, v_env_473_, v_entry_464_, v_asyncMode_484_, v___x_467_);
v___x_486_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__5);
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 5, v___x_486_);
lean_ctor_set(v___x_482_, 0, v___x_485_);
v___x_488_ = v___x_482_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_485_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_nextMacroScope_474_);
lean_ctor_set(v_reuseFailAlloc_507_, 2, v_ngen_475_);
lean_ctor_set(v_reuseFailAlloc_507_, 3, v_auxDeclNGen_476_);
lean_ctor_set(v_reuseFailAlloc_507_, 4, v_traceState_477_);
lean_ctor_set(v_reuseFailAlloc_507_, 5, v___x_486_);
lean_ctor_set(v_reuseFailAlloc_507_, 6, v_messages_478_);
lean_ctor_set(v_reuseFailAlloc_507_, 7, v_infoState_479_);
lean_ctor_set(v_reuseFailAlloc_507_, 8, v_snapshotTasks_480_);
v___x_488_ = v_reuseFailAlloc_507_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v_mctx_491_; lean_object* v_zetaDeltaFVarIds_492_; lean_object* v_postponed_493_; lean_object* v_diag_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_505_; 
v___x_489_ = lean_st_ref_set(v___y_470_, v___x_488_);
v___x_490_ = lean_st_ref_take(v___y_469_);
v_mctx_491_ = lean_ctor_get(v___x_490_, 0);
v_zetaDeltaFVarIds_492_ = lean_ctor_get(v___x_490_, 2);
v_postponed_493_ = lean_ctor_get(v___x_490_, 3);
v_diag_494_ = lean_ctor_get(v___x_490_, 4);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v___x_490_, 1);
lean_dec(v_unused_506_);
v___x_496_ = v___x_490_;
v_isShared_497_ = v_isSharedCheck_505_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_diag_494_);
lean_inc(v_postponed_493_);
lean_inc(v_zetaDeltaFVarIds_492_);
lean_inc(v_mctx_491_);
lean_dec(v___x_490_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_505_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_498_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__6);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v___x_498_);
v___x_500_ = v___x_496_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_mctx_491_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_498_);
lean_ctor_set(v_reuseFailAlloc_504_, 2, v_zetaDeltaFVarIds_492_);
lean_ctor_set(v_reuseFailAlloc_504_, 3, v_postponed_493_);
lean_ctor_set(v_reuseFailAlloc_504_, 4, v_diag_494_);
v___x_500_ = v_reuseFailAlloc_504_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_st_ref_set(v___y_469_, v___x_500_);
v___x_502_ = lean_box(0);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___boxed(lean_object* v_mod_550_, lean_object* v_isMeta_551_, lean_object* v_hint_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
uint8_t v_isMeta_boxed_560_; lean_object* v_res_561_; 
v_isMeta_boxed_560_ = lean_unbox(v_isMeta_551_);
v_res_561_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0(v_mod_550_, v_isMeta_boxed_560_, v_hint_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__1(lean_object* v___x_562_, lean_object* v_declName_563_, lean_object* v_as_564_, size_t v_sz_565_, size_t v_i_566_, lean_object* v_b_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
uint8_t v___x_575_; 
v___x_575_ = lean_usize_dec_lt(v_i_566_, v_sz_565_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; 
lean_dec(v_declName_563_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v_b_567_);
return v___x_576_;
}
else
{
lean_object* v___x_577_; lean_object* v_modules_578_; lean_object* v___x_579_; lean_object* v_a_580_; lean_object* v___x_581_; lean_object* v_toImport_582_; lean_object* v_module_583_; uint8_t v___x_584_; lean_object* v___x_585_; 
v___x_577_ = l_Lean_Environment_header(v___x_562_);
v_modules_578_ = lean_ctor_get(v___x_577_, 3);
lean_inc_ref(v_modules_578_);
lean_dec_ref(v___x_577_);
v___x_579_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_580_ = lean_array_uget_borrowed(v_as_564_, v_i_566_);
v___x_581_ = lean_array_get(v___x_579_, v_modules_578_, v_a_580_);
lean_dec_ref(v_modules_578_);
v_toImport_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc_ref(v_toImport_582_);
lean_dec(v___x_581_);
v_module_583_ = lean_ctor_get(v_toImport_582_, 0);
lean_inc(v_module_583_);
lean_dec_ref(v_toImport_582_);
v___x_584_ = 0;
lean_inc(v_declName_563_);
v___x_585_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0(v_module_583_, v___x_584_, v_declName_563_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v___x_586_; size_t v___x_587_; size_t v___x_588_; 
lean_dec_ref(v___x_585_);
v___x_586_ = lean_box(0);
v___x_587_ = ((size_t)1ULL);
v___x_588_ = lean_usize_add(v_i_566_, v___x_587_);
v_i_566_ = v___x_588_;
v_b_567_ = v___x_586_;
goto _start;
}
else
{
lean_dec(v_declName_563_);
return v___x_585_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__1___boxed(lean_object* v___x_590_, lean_object* v_declName_591_, lean_object* v_as_592_, lean_object* v_sz_593_, lean_object* v_i_594_, lean_object* v_b_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
size_t v_sz_boxed_603_; size_t v_i_boxed_604_; lean_object* v_res_605_; 
v_sz_boxed_603_ = lean_unbox_usize(v_sz_593_);
lean_dec(v_sz_593_);
v_i_boxed_604_ = lean_unbox_usize(v_i_594_);
lean_dec(v_i_594_);
v_res_605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__1(v___x_590_, v_declName_591_, v_as_592_, v_sz_boxed_603_, v_i_boxed_604_, v_b_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_);
lean_dec(v___y_601_);
lean_dec_ref(v___y_600_);
lean_dec(v___y_599_);
lean_dec_ref(v___y_598_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec_ref(v_as_592_);
lean_dec_ref(v___x_590_);
return v_res_605_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__2(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_608_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__1));
v___x_609_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__0));
v___x_610_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_609_, v___x_608_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0(lean_object* v_declName_613_, uint8_t v_isMeta_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
lean_object* v___x_622_; lean_object* v_env_626_; lean_object* v___y_628_; lean_object* v___x_641_; 
v___x_622_ = lean_st_ref_get(v___y_620_);
v_env_626_ = lean_ctor_get(v___x_622_, 0);
lean_inc_ref(v_env_626_);
lean_dec(v___x_622_);
v___x_641_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_626_, v_declName_613_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_dec_ref(v_env_626_);
lean_dec(v_declName_613_);
goto v___jp_623_;
}
else
{
lean_object* v_val_642_; lean_object* v___x_643_; lean_object* v_modules_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v_val_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_val_642_);
lean_dec_ref(v___x_641_);
v___x_643_ = l_Lean_Environment_header(v_env_626_);
v_modules_644_ = lean_ctor_get(v___x_643_, 3);
lean_inc_ref(v_modules_644_);
lean_dec_ref(v___x_643_);
v___x_645_ = lean_array_get_size(v_modules_644_);
v___x_646_ = lean_nat_dec_lt(v_val_642_, v___x_645_);
if (v___x_646_ == 0)
{
lean_dec_ref(v_modules_644_);
lean_dec(v_val_642_);
lean_dec_ref(v_env_626_);
lean_dec(v_declName_613_);
goto v___jp_623_;
}
else
{
lean_object* v___x_647_; lean_object* v_env_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___y_652_; 
v___x_647_ = lean_st_ref_get(v___y_620_);
v_env_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc_ref(v_env_648_);
lean_dec(v___x_647_);
v___x_649_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__2);
v___x_650_ = lean_array_fget(v_modules_644_, v_val_642_);
lean_dec(v_val_642_);
lean_dec_ref(v_modules_644_);
if (v_isMeta_614_ == 0)
{
lean_dec_ref(v_env_648_);
v___y_652_ = v_isMeta_614_;
goto v___jp_651_;
}
else
{
uint8_t v___x_663_; 
lean_inc(v_declName_613_);
v___x_663_ = l_Lean_isMarkedMeta(v_env_648_, v_declName_613_);
if (v___x_663_ == 0)
{
v___y_652_ = v_isMeta_614_;
goto v___jp_651_;
}
else
{
uint8_t v___x_664_; 
v___x_664_ = 0;
v___y_652_ = v___x_664_;
goto v___jp_651_;
}
}
v___jp_651_:
{
lean_object* v_toImport_653_; lean_object* v_module_654_; lean_object* v___x_655_; 
v_toImport_653_ = lean_ctor_get(v___x_650_, 0);
lean_inc_ref(v_toImport_653_);
lean_dec(v___x_650_);
v_module_654_ = lean_ctor_get(v_toImport_653_, 0);
lean_inc(v_module_654_);
lean_dec_ref(v_toImport_653_);
lean_inc(v_declName_613_);
v___x_655_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0(v_module_654_, v___y_652_, v_declName_613_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
lean_dec_ref(v___x_655_);
v___x_656_ = l_Lean_indirectModUseExt;
v___x_657_ = lean_box(1);
v___x_658_ = lean_box(0);
lean_inc_ref(v_env_626_);
v___x_659_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_649_, v___x_656_, v_env_626_, v___x_657_, v___x_658_);
v___x_660_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg(v___x_659_, v_declName_613_);
lean_dec(v___x_659_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v___x_661_; 
v___x_661_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__3));
v___y_628_ = v___x_661_;
goto v___jp_627_;
}
else
{
lean_object* v_val_662_; 
v_val_662_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_val_662_);
lean_dec_ref(v___x_660_);
v___y_628_ = v_val_662_;
goto v___jp_627_;
}
}
else
{
lean_dec_ref(v_env_626_);
lean_dec(v_declName_613_);
return v___x_655_;
}
}
}
}
v___jp_623_:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = lean_box(0);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
v___jp_627_:
{
lean_object* v___x_629_; size_t v_sz_630_; size_t v___x_631_; lean_object* v___x_632_; 
v___x_629_ = lean_box(0);
v_sz_630_ = lean_array_size(v___y_628_);
v___x_631_ = ((size_t)0ULL);
v___x_632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__1(v_env_626_, v_declName_613_, v___y_628_, v_sz_630_, v___x_631_, v___x_629_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_);
lean_dec_ref(v___y_628_);
lean_dec_ref(v_env_626_);
if (lean_obj_tag(v___x_632_) == 0)
{
lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_632_);
if (v_isSharedCheck_639_ == 0)
{
lean_object* v_unused_640_; 
v_unused_640_ = lean_ctor_get(v___x_632_, 0);
lean_dec(v_unused_640_);
v___x_634_ = v___x_632_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_dec(v___x_632_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_629_);
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_629_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
else
{
return v___x_632_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___boxed(lean_object* v_declName_665_, lean_object* v_isMeta_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
uint8_t v_isMeta_boxed_674_; lean_object* v_res_675_; 
v_isMeta_boxed_674_ = lean_unbox(v_isMeta_666_);
v_res_675_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0(v_declName_665_, v_isMeta_boxed_674_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
return v_res_675_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__9(lean_object* v_opts_676_, lean_object* v_opt_677_){
_start:
{
lean_object* v_name_678_; lean_object* v_defValue_679_; lean_object* v_map_680_; lean_object* v___x_681_; 
v_name_678_ = lean_ctor_get(v_opt_677_, 0);
v_defValue_679_ = lean_ctor_get(v_opt_677_, 1);
v_map_680_ = lean_ctor_get(v_opts_676_, 0);
v___x_681_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_680_, v_name_678_);
if (lean_obj_tag(v___x_681_) == 0)
{
uint8_t v___x_682_; 
v___x_682_ = lean_unbox(v_defValue_679_);
return v___x_682_;
}
else
{
lean_object* v_val_683_; 
v_val_683_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_val_683_);
lean_dec_ref(v___x_681_);
if (lean_obj_tag(v_val_683_) == 1)
{
uint8_t v_v_684_; 
v_v_684_ = lean_ctor_get_uint8(v_val_683_, 0);
lean_dec_ref(v_val_683_);
return v_v_684_;
}
else
{
uint8_t v___x_685_; 
lean_dec(v_val_683_);
v___x_685_ = lean_unbox(v_defValue_679_);
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__9___boxed(lean_object* v_opts_686_, lean_object* v_opt_687_){
_start:
{
uint8_t v_res_688_; lean_object* v_r_689_; 
v_res_688_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__9(v_opts_686_, v_opt_687_);
lean_dec_ref(v_opt_687_);
lean_dec_ref(v_opts_686_);
v_r_689_ = lean_box(v_res_688_);
return v_r_689_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__0(void){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_box(1);
v___x_691_ = l_Lean_MessageData_ofFormat(v___x_690_);
return v___x_691_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__3(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__2));
v___x_696_ = l_Lean_MessageData_ofFormat(v___x_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10(lean_object* v_x_697_, lean_object* v_x_698_){
_start:
{
if (lean_obj_tag(v_x_698_) == 0)
{
return v_x_697_;
}
else
{
lean_object* v_head_699_; lean_object* v_tail_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_722_; 
v_head_699_ = lean_ctor_get(v_x_698_, 0);
v_tail_700_ = lean_ctor_get(v_x_698_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_x_698_);
if (v_isSharedCheck_722_ == 0)
{
v___x_702_ = v_x_698_;
v_isShared_703_ = v_isSharedCheck_722_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_tail_700_);
lean_inc(v_head_699_);
lean_dec(v_x_698_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_722_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_before_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_720_; 
v_before_704_ = lean_ctor_get(v_head_699_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v_head_699_);
if (v_isSharedCheck_720_ == 0)
{
lean_object* v_unused_721_; 
v_unused_721_ = lean_ctor_get(v_head_699_, 1);
lean_dec(v_unused_721_);
v___x_706_ = v_head_699_;
v_isShared_707_ = v_isSharedCheck_720_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_before_704_);
lean_dec(v_head_699_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_720_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_708_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__0);
if (v_isShared_707_ == 0)
{
lean_ctor_set_tag(v___x_706_, 7);
lean_ctor_set(v___x_706_, 1, v___x_708_);
lean_ctor_set(v___x_706_, 0, v_x_697_);
v___x_710_ = v___x_706_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_x_697_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_708_);
v___x_710_ = v_reuseFailAlloc_719_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__3);
if (v_isShared_703_ == 0)
{
lean_ctor_set_tag(v___x_702_, 7);
lean_ctor_set(v___x_702_, 1, v___x_711_);
lean_ctor_set(v___x_702_, 0, v___x_710_);
v___x_713_ = v___x_702_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v___x_711_);
v___x_713_ = v_reuseFailAlloc_718_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_714_ = l_Lean_MessageData_ofSyntax(v_before_704_);
v___x_715_ = l_Lean_indentD(v___x_714_);
v___x_716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_716_, 0, v___x_713_);
lean_ctor_set(v___x_716_, 1, v___x_715_);
v_x_697_ = v___x_716_;
v_x_698_ = v_tail_700_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__1));
v___x_727_ = l_Lean_MessageData_ofFormat(v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg(lean_object* v_msgData_728_, lean_object* v_macroStack_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_options_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v_options_732_ = lean_ctor_get(v___y_730_, 2);
v___x_733_ = l_Lean_Elab_pp_macroStack;
v___x_734_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__9(v_options_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; 
lean_dec(v_macroStack_729_);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v_msgData_728_);
return v___x_735_;
}
else
{
if (lean_obj_tag(v_macroStack_729_) == 0)
{
lean_object* v___x_736_; 
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v_msgData_728_);
return v___x_736_;
}
else
{
lean_object* v_head_737_; lean_object* v_after_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_753_; 
v_head_737_ = lean_ctor_get(v_macroStack_729_, 0);
lean_inc(v_head_737_);
v_after_738_ = lean_ctor_get(v_head_737_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v_head_737_);
if (v_isSharedCheck_753_ == 0)
{
lean_object* v_unused_754_; 
v_unused_754_ = lean_ctor_get(v_head_737_, 0);
lean_dec(v_unused_754_);
v___x_740_ = v_head_737_;
v_isShared_741_ = v_isSharedCheck_753_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_after_738_);
lean_dec(v_head_737_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_753_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_742_; lean_object* v___x_744_; 
v___x_742_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___closed__0);
if (v_isShared_741_ == 0)
{
lean_ctor_set_tag(v___x_740_, 7);
lean_ctor_set(v___x_740_, 1, v___x_742_);
lean_ctor_set(v___x_740_, 0, v_msgData_728_);
v___x_744_ = v___x_740_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_msgData_728_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v___x_742_);
v___x_744_ = v_reuseFailAlloc_752_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_msgData_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_745_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__2);
v___x_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = l_Lean_MessageData_ofSyntax(v_after_738_);
v___x_748_ = l_Lean_indentD(v___x_747_);
v_msgData_749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_749_, 0, v___x_746_);
lean_ctor_set(v_msgData_749_, 1, v___x_748_);
v___x_750_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10(v_msgData_749_, v_macroStack_729_);
v___x_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
return v___x_751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___boxed(lean_object* v_msgData_755_, lean_object* v_macroStack_756_, lean_object* v___y_757_, lean_object* v___y_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg(v_msgData_755_, v_macroStack_756_, v___y_757_);
lean_dec_ref(v___y_757_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg(lean_object* v_msg_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_ref_768_; lean_object* v___x_769_; lean_object* v_a_770_; lean_object* v_macroStack_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_782_; 
v_ref_768_ = lean_ctor_get(v___y_765_, 5);
v___x_769_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__4(v_msg_760_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref(v___x_769_);
v_macroStack_771_ = lean_ctor_get(v___y_761_, 1);
lean_inc_n(v_macroStack_771_, 2);
v___x_772_ = l_Lean_Elab_getBetterRef(v_ref_768_, v_macroStack_771_);
v___x_773_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg(v_a_770_, v_macroStack_771_, v___y_765_);
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_782_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_782_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v___x_772_);
lean_ctor_set(v___x_778_, 1, v_a_774_);
if (v_isShared_777_ == 0)
{
lean_ctor_set_tag(v___x_776_, 1);
lean_ctor_set(v___x_776_, 0, v___x_778_);
v___x_780_ = v___x_776_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg___boxed(lean_object* v_msg_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg(v_msg_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_, v___y_789_);
lean_dec(v___y_789_);
lean_dec_ref(v___y_788_);
lean_dec(v___y_787_);
lean_dec_ref(v___y_786_);
lean_dec(v___y_785_);
lean_dec_ref(v___y_784_);
return v_res_791_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__0));
v___x_794_ = l_Lean_stringToMessageData(v___x_793_);
return v___x_794_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__2));
v___x_797_ = l_Lean_stringToMessageData(v___x_796_);
return v___x_797_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__5(void){
_start:
{
lean_object* v___x_799_; lean_object* v___x_800_; 
v___x_799_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__4));
v___x_800_ = l_Lean_stringToMessageData(v___x_799_);
return v___x_800_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__7(void){
_start:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__6));
v___x_803_ = l_Lean_stringToMessageData(v___x_802_);
return v___x_803_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__8(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_));
v___x_805_ = l_Lean_MessageData_ofName(v___x_804_);
return v___x_805_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__9(void){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v___x_806_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__8);
v___x_807_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__7);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v___x_806_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(lean_object* v_optConfig_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; uint8_t v___y_834_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; lean_object* v___y_851_; uint8_t v_recover_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; uint8_t v___x_862_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; 
v_recover_856_ = lean_ctor_get_uint8(v_a_816_, sizeof(void*)*1);
lean_inc(v_optConfig_815_);
v___x_857_ = l_Lean_Parser_Tactic_getConfigItems(v_optConfig_815_);
v___x_858_ = l_Lean_Elab_Tactic_mkConfigItemViews(v___x_857_);
v___x_859_ = lean_array_get_size(v___x_858_);
v___x_860_ = lean_unsigned_to_nat(0u);
v___x_861_ = lean_nat_dec_eq(v___x_859_, v___x_860_);
v___x_862_ = 1;
if (v___x_861_ == 0)
{
lean_object* v___x_913_; lean_object* v_fileName_914_; lean_object* v_fileMap_915_; lean_object* v_options_916_; lean_object* v_currRecDepth_917_; lean_object* v_maxRecDepth_918_; lean_object* v_ref_919_; lean_object* v_currNamespace_920_; lean_object* v_openDecls_921_; lean_object* v_initHeartbeats_922_; lean_object* v_maxHeartbeats_923_; lean_object* v_quotContext_924_; lean_object* v_currMacroScope_925_; uint8_t v_diag_926_; lean_object* v_cancelTk_x3f_927_; uint8_t v_suppressElabErrors_928_; lean_object* v_inheritedTraceOptions_929_; lean_object* v_env_930_; lean_object* v_ref_931_; lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_913_ = lean_st_ref_get(v_a_822_);
v_fileName_914_ = lean_ctor_get(v_a_821_, 0);
v_fileMap_915_ = lean_ctor_get(v_a_821_, 1);
v_options_916_ = lean_ctor_get(v_a_821_, 2);
v_currRecDepth_917_ = lean_ctor_get(v_a_821_, 3);
v_maxRecDepth_918_ = lean_ctor_get(v_a_821_, 4);
v_ref_919_ = lean_ctor_get(v_a_821_, 5);
v_currNamespace_920_ = lean_ctor_get(v_a_821_, 6);
v_openDecls_921_ = lean_ctor_get(v_a_821_, 7);
v_initHeartbeats_922_ = lean_ctor_get(v_a_821_, 8);
v_maxHeartbeats_923_ = lean_ctor_get(v_a_821_, 9);
v_quotContext_924_ = lean_ctor_get(v_a_821_, 10);
v_currMacroScope_925_ = lean_ctor_get(v_a_821_, 11);
v_diag_926_ = lean_ctor_get_uint8(v_a_821_, sizeof(void*)*14);
v_cancelTk_x3f_927_ = lean_ctor_get(v_a_821_, 12);
v_suppressElabErrors_928_ = lean_ctor_get_uint8(v_a_821_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_929_ = lean_ctor_get(v_a_821_, 13);
v_env_930_ = lean_ctor_get(v___x_913_, 0);
lean_inc_ref(v_env_930_);
lean_dec(v___x_913_);
v_ref_931_ = l_Lean_replaceRef(v_optConfig_815_, v_ref_919_);
lean_dec(v_optConfig_815_);
lean_inc_ref(v_inheritedTraceOptions_929_);
lean_inc(v_cancelTk_x3f_927_);
lean_inc(v_currMacroScope_925_);
lean_inc(v_quotContext_924_);
lean_inc(v_maxHeartbeats_923_);
lean_inc(v_initHeartbeats_922_);
lean_inc(v_openDecls_921_);
lean_inc(v_currNamespace_920_);
lean_inc(v_maxRecDepth_918_);
lean_inc(v_currRecDepth_917_);
lean_inc_ref(v_options_916_);
lean_inc_ref(v_fileMap_915_);
lean_inc_ref(v_fileName_914_);
v___x_932_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_932_, 0, v_fileName_914_);
lean_ctor_set(v___x_932_, 1, v_fileMap_915_);
lean_ctor_set(v___x_932_, 2, v_options_916_);
lean_ctor_set(v___x_932_, 3, v_currRecDepth_917_);
lean_ctor_set(v___x_932_, 4, v_maxRecDepth_918_);
lean_ctor_set(v___x_932_, 5, v_ref_931_);
lean_ctor_set(v___x_932_, 6, v_currNamespace_920_);
lean_ctor_set(v___x_932_, 7, v_openDecls_921_);
lean_ctor_set(v___x_932_, 8, v_initHeartbeats_922_);
lean_ctor_set(v___x_932_, 9, v_maxHeartbeats_923_);
lean_ctor_set(v___x_932_, 10, v_quotContext_924_);
lean_ctor_set(v___x_932_, 11, v_currMacroScope_925_);
lean_ctor_set(v___x_932_, 12, v_cancelTk_x3f_927_);
lean_ctor_set(v___x_932_, 13, v_inheritedTraceOptions_929_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*14, v_diag_926_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*14 + 1, v_suppressElabErrors_928_);
v___x_933_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_));
v___x_934_ = l_Lean_Environment_contains(v_env_930_, v___x_933_, v___x_862_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec_ref(v___x_858_);
v___x_935_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__9);
v___x_936_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg(v___x_935_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v___x_932_, v_a_822_);
lean_dec_ref(v___x_932_);
v_a_937_ = lean_ctor_get(v___x_936_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_936_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_936_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_936_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
else
{
v___y_864_ = v_a_817_;
v___y_865_ = v_a_818_;
v___y_866_ = v_a_819_;
v___y_867_ = v_a_820_;
v___y_868_ = v___x_932_;
v___y_869_ = v_a_822_;
goto v___jp_863_;
}
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; 
lean_dec_ref(v___x_858_);
lean_dec(v_optConfig_815_);
v___x_945_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__10));
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
return v___x_946_;
}
v___jp_824_:
{
if (v___y_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
lean_dec_ref(v___y_831_);
v___x_835_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__1);
v___x_836_ = l_Lean_MessageData_ofExpr(v___y_833_);
v___x_837_ = l_Lean_indentD(v___x_836_);
v___x_838_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_835_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__3);
v___x_840_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_840_, 0, v___x_838_);
lean_ctor_set(v___x_840_, 1, v___x_839_);
v___x_841_ = l_Lean_Exception_toMessageData(v___y_827_);
v___x_842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg(v___x_842_, v___y_832_, v___y_826_, v___y_830_, v___y_828_, v___y_825_, v___y_829_);
lean_dec_ref(v___y_825_);
return v___x_843_;
}
else
{
lean_dec_ref(v___y_833_);
lean_dec_ref(v___y_827_);
lean_dec_ref(v___y_825_);
return v___y_831_;
}
}
v___jp_844_:
{
lean_object* v___x_852_; 
lean_inc_ref(v___y_845_);
v___x_852_ = l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_(v___y_845_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_dec_ref(v___y_850_);
lean_dec_ref(v___y_845_);
return v___x_852_;
}
else
{
lean_object* v_a_853_; uint8_t v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
v___x_854_ = l_Lean_Exception_isInterrupt(v_a_853_);
if (v___x_854_ == 0)
{
uint8_t v___x_855_; 
lean_inc(v_a_853_);
v___x_855_ = l_Lean_Exception_isRuntime(v_a_853_);
v___y_825_ = v___y_850_;
v___y_826_ = v___y_847_;
v___y_827_ = v_a_853_;
v___y_828_ = v___y_849_;
v___y_829_ = v___y_851_;
v___y_830_ = v___y_848_;
v___y_831_ = v___x_852_;
v___y_832_ = v___y_846_;
v___y_833_ = v___y_845_;
v___y_834_ = v___x_855_;
goto v___jp_824_;
}
else
{
v___y_825_ = v___y_850_;
v___y_826_ = v___y_847_;
v___y_827_ = v_a_853_;
v___y_828_ = v___y_849_;
v___y_829_ = v___y_851_;
v___y_830_ = v___y_848_;
v___y_831_ = v___x_852_;
v___y_832_ = v___y_846_;
v___y_833_ = v___y_845_;
v___y_834_ = v___x_854_;
goto v___jp_824_;
}
}
}
v___jp_863_:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_));
v___x_871_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0(v___x_870_, v___x_862_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v___x_872_; 
lean_dec_ref(v___x_871_);
v___x_872_ = l_Lean_Elab_Tactic_elabConfig(v_recover_856_, v___x_870_, v___x_858_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_896_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_896_ == 0)
{
v___x_875_ = v___x_872_;
v_isShared_876_ = v_isSharedCheck_896_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_872_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_896_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
uint8_t v___x_877_; 
v___x_877_ = l_Lean_Expr_hasSyntheticSorry(v_a_873_);
if (v___x_877_ == 0)
{
uint8_t v___x_878_; 
lean_del_object(v___x_875_);
v___x_878_ = l_Lean_Expr_hasSorry(v_a_873_);
if (v___x_878_ == 0)
{
v___y_845_ = v_a_873_;
v___y_846_ = v___y_864_;
v___y_847_ = v___y_865_;
v___y_848_ = v___y_866_;
v___y_849_ = v___y_867_;
v___y_850_ = v___y_868_;
v___y_851_ = v___y_869_;
goto v___jp_844_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec(v_a_873_);
v___x_879_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__5);
v___x_880_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg(v___x_879_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec_ref(v___y_868_);
v_a_881_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_880_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_880_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_894_; 
lean_dec(v_a_873_);
lean_dec_ref(v___y_868_);
v___x_889_ = lean_unsigned_to_nat(10u);
v___x_890_ = lean_unsigned_to_nat(100000u);
v___x_891_ = 0;
v___x_892_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_892_, 0, v___x_889_);
lean_ctor_set(v___x_892_, 1, v___x_890_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*2, v___x_862_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*2 + 1, v___x_862_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*2 + 2, v___x_861_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*2 + 3, v___x_862_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*2 + 4, v___x_862_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*2 + 5, v___x_862_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*2 + 6, v___x_862_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*2 + 7, v___x_862_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*2 + 8, v___x_861_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*2 + 9, v___x_861_);
lean_ctor_set_uint8(v___x_892_, sizeof(void*)*2 + 10, v___x_891_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 0, v___x_892_);
v___x_894_ = v___x_875_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
lean_dec_ref(v___y_868_);
v_a_897_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_872_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_872_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec_ref(v___y_868_);
lean_dec_ref(v___x_858_);
v_a_905_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_871_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_871_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___boxed(lean_object* v_optConfig_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(v_optConfig_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_);
lean_dec(v_a_954_);
lean_dec_ref(v_a_953_);
lean_dec(v_a_952_);
lean_dec_ref(v_a_951_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec_ref(v_a_948_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig(lean_object* v_optConfig_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(v_optConfig_957_, v_a_958_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___boxed(lean_object* v_optConfig_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig(v_optConfig_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_);
lean_dec(v_a_976_);
lean_dec_ref(v_a_975_);
lean_dec(v_a_974_);
lean_dec_ref(v_a_973_);
lean_dec(v_a_972_);
lean_dec_ref(v_a_971_);
lean_dec(v_a_970_);
lean_dec_ref(v_a_969_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1(lean_object* v_00_u03b1_979_, lean_object* v_msg_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg(v_msg_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_, v___y_986_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___boxed(lean_object* v_00_u03b1_989_, lean_object* v_msg_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1(v_00_u03b1_989_, v_msg_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2(lean_object* v_00_u03b2_999_, lean_object* v_m_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg(v_m_1000_, v_a_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1003_, lean_object* v_m_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2(v_00_u03b2_1003_, v_m_1004_, v_a_1005_);
lean_dec(v_a_1005_);
lean_dec_ref(v_m_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5(lean_object* v_msgData_1007_, lean_object* v_macroStack_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg(v_msgData_1007_, v_macroStack_1008_, v___y_1013_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___boxed(lean_object* v_msgData_1017_, lean_object* v_macroStack_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5(v_msgData_1017_, v_macroStack_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
return v_res_1026_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1027_, lean_object* v_x_1028_, lean_object* v_x_1029_){
_start:
{
uint8_t v___x_1030_; 
v___x_1030_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___redArg(v_x_1028_, v_x_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_){
_start:
{
uint8_t v_res_1034_; lean_object* v_r_1035_; 
v_res_1034_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1(v_00_u03b2_1031_, v_x_1032_, v_x_1033_);
lean_dec_ref(v_x_1033_);
lean_dec_ref(v_x_1032_);
v_r_1035_ = lean_box(v_res_1034_);
return v_r_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2(lean_object* v_cls_1036_, lean_object* v_msg_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg(v_cls_1036_, v_msg_1037_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1046_, lean_object* v_msg_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2(v_cls_1046_, v_msg_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec_ref(v___y_1050_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1056_, lean_object* v_a_1057_, lean_object* v_x_1058_){
_start:
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__5___redArg(v_a_1057_, v_x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1060_, lean_object* v_a_1061_, lean_object* v_x_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__5(v_00_u03b2_1060_, v_a_1061_, v_x_1062_);
lean_dec(v_x_1062_);
lean_dec(v_a_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1064_, lean_object* v_x_1065_, size_t v_x_1066_, lean_object* v_x_1067_){
_start:
{
uint8_t v___x_1068_; 
v___x_1068_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1065_, v_x_1066_, v_x_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1069_, lean_object* v_x_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
size_t v_x_13644__boxed_1073_; uint8_t v_res_1074_; lean_object* v_r_1075_; 
v_x_13644__boxed_1073_ = lean_unbox_usize(v_x_1071_);
lean_dec(v_x_1071_);
v_res_1074_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_1069_, v_x_1070_, v_x_13644__boxed_1073_, v_x_1072_);
lean_dec_ref(v_x_1072_);
lean_dec_ref(v_x_1070_);
v_r_1075_ = lean_box(v_res_1074_);
return v_r_1075_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_1076_, lean_object* v_keys_1077_, lean_object* v_vals_1078_, lean_object* v_heq_1079_, lean_object* v_i_1080_, lean_object* v_k_1081_){
_start:
{
uint8_t v___x_1082_; 
v___x_1082_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__9___redArg(v_keys_1077_, v_i_1080_, v_k_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__9___boxed(lean_object* v_00_u03b2_1083_, lean_object* v_keys_1084_, lean_object* v_vals_1085_, lean_object* v_heq_1086_, lean_object* v_i_1087_, lean_object* v_k_1088_){
_start:
{
uint8_t v_res_1089_; lean_object* v_r_1090_; 
v_res_1089_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__9(v_00_u03b2_1083_, v_keys_1084_, v_vals_1085_, v_heq_1086_, v_i_1087_, v_k_1088_);
lean_dec_ref(v_k_1088_);
lean_dec_ref(v_vals_1085_);
lean_dec_ref(v_keys_1084_);
v_r_1090_ = lean_box(v_res_1089_);
return v_r_1090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1104_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_));
v___x_1105_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_));
v___x_1106_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_));
v___x_1107_ = l_Lean_Meta_registerSimpAttr(v___x_1104_, v___x_1105_, v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2____boxed(lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_();
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1123_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_));
v___x_1124_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_));
v___x_1125_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_));
v___x_1126_ = l_Lean_Meta_registerSimpAttr(v___x_1123_, v___x_1124_, v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2____boxed(lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_();
return v_res_1128_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0(void){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1(void){
_start:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1130_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0);
v___x_1131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1132_){
_start:
{
lean_object* v___x_1133_; 
v___x_1133_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1);
return v___x_1133_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0(lean_box(0));
return v___x_1135_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_, &l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_);
v___x_1137_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_, &l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_);
v___x_1138_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1137_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
lean_ctor_set(v___x_1138_, 2, v___x_1136_);
lean_ctor_set(v___x_1138_, 3, v___x_1136_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_, &l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_);
v___x_1141_ = lean_st_mk_ref(v___x_1140_);
v___x_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2____boxed(lean_object* v_a_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_();
return v_res_1144_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; 
v___x_1149_ = l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef;
v___x_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1160_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_));
v___x_1161_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_));
v___x_1162_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_, &l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_);
v___x_1163_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_));
v___x_1164_ = l_Lean_Meta_Simp_registerSimprocAttr(v___x_1160_, v___x_1161_, v___x_1162_, v___x_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2____boxed(lean_object* v_a_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_();
return v_res_1166_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1170_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1);
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
lean_ctor_set(v___x_1172_, 2, v___x_1171_);
lean_ctor_set(v___x_1172_, 3, v___x_1170_);
lean_ctor_set(v___x_1172_, 4, v___x_1170_);
lean_ctor_set(v___x_1172_, 5, v___x_1170_);
lean_ctor_set(v___x_1172_, 6, v___x_1170_);
lean_ctor_set(v___x_1172_, 7, v___x_1170_);
lean_ctor_set(v___x_1172_, 8, v___x_1170_);
return v___x_1172_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = lean_unsigned_to_nat(32u);
v___x_1174_ = lean_mk_empty_array_with_capacity(v___x_1173_);
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1176_ = ((size_t)5ULL);
v___x_1177_ = lean_unsigned_to_nat(0u);
v___x_1178_ = lean_unsigned_to_nat(32u);
v___x_1179_ = lean_mk_empty_array_with_capacity(v___x_1178_);
v___x_1180_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3);
v___x_1181_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v___x_1179_);
lean_ctor_set(v___x_1181_, 2, v___x_1177_);
lean_ctor_set(v___x_1181_, 3, v___x_1177_);
lean_ctor_set_usize(v___x_1181_, 4, v___x_1176_);
return v___x_1181_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1182_ = lean_box(1);
v___x_1183_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4);
v___x_1184_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1);
v___x_1185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1185_, 0, v___x_1184_);
lean_ctor_set(v___x_1185_, 1, v___x_1183_);
lean_ctor_set(v___x_1185_, 2, v___x_1182_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0(lean_object* v_msgData_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; lean_object* v_env_1191_; lean_object* v_options_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1190_ = lean_st_ref_get(v___y_1188_);
v_env_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc_ref(v_env_1191_);
lean_dec(v___x_1190_);
v_options_1192_ = lean_ctor_get(v___y_1187_, 2);
v___x_1193_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2);
v___x_1194_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_1192_);
v___x_1195_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1195_, 0, v_env_1191_);
lean_ctor_set(v___x_1195_, 1, v___x_1193_);
lean_ctor_set(v___x_1195_, 2, v___x_1194_);
lean_ctor_set(v___x_1195_, 3, v_options_1192_);
v___x_1196_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
lean_ctor_set(v___x_1196_, 1, v_msgData_1186_);
v___x_1197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___boxed(lean_object* v_msgData_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0(v_msgData_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(lean_object* v_msg_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_ref_1207_; lean_object* v___x_1208_; lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1217_; 
v_ref_1207_ = lean_ctor_get(v___y_1204_, 5);
v___x_1208_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0(v_msg_1203_, v___y_1204_, v___y_1205_);
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
lean_inc(v_ref_1207_);
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v_ref_1207_);
lean_ctor_set(v___x_1213_, 1, v_a_1209_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set_tag(v___x_1211_, 1);
lean_ctor_set(v___x_1211_, 0, v___x_1213_);
v___x_1215_ = v___x_1211_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg___boxed(lean_object* v_msg_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(v_msg_1218_, v___y_1219_, v___y_1220_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_ref_1223_, lean_object* v_msg_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v_fileName_1228_; lean_object* v_fileMap_1229_; lean_object* v_options_1230_; lean_object* v_currRecDepth_1231_; lean_object* v_maxRecDepth_1232_; lean_object* v_ref_1233_; lean_object* v_currNamespace_1234_; lean_object* v_openDecls_1235_; lean_object* v_initHeartbeats_1236_; lean_object* v_maxHeartbeats_1237_; lean_object* v_quotContext_1238_; lean_object* v_currMacroScope_1239_; uint8_t v_diag_1240_; lean_object* v_cancelTk_x3f_1241_; uint8_t v_suppressElabErrors_1242_; lean_object* v_inheritedTraceOptions_1243_; lean_object* v_ref_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v_fileName_1228_ = lean_ctor_get(v___y_1225_, 0);
v_fileMap_1229_ = lean_ctor_get(v___y_1225_, 1);
v_options_1230_ = lean_ctor_get(v___y_1225_, 2);
v_currRecDepth_1231_ = lean_ctor_get(v___y_1225_, 3);
v_maxRecDepth_1232_ = lean_ctor_get(v___y_1225_, 4);
v_ref_1233_ = lean_ctor_get(v___y_1225_, 5);
v_currNamespace_1234_ = lean_ctor_get(v___y_1225_, 6);
v_openDecls_1235_ = lean_ctor_get(v___y_1225_, 7);
v_initHeartbeats_1236_ = lean_ctor_get(v___y_1225_, 8);
v_maxHeartbeats_1237_ = lean_ctor_get(v___y_1225_, 9);
v_quotContext_1238_ = lean_ctor_get(v___y_1225_, 10);
v_currMacroScope_1239_ = lean_ctor_get(v___y_1225_, 11);
v_diag_1240_ = lean_ctor_get_uint8(v___y_1225_, sizeof(void*)*14);
v_cancelTk_x3f_1241_ = lean_ctor_get(v___y_1225_, 12);
v_suppressElabErrors_1242_ = lean_ctor_get_uint8(v___y_1225_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1243_ = lean_ctor_get(v___y_1225_, 13);
v_ref_1244_ = l_Lean_replaceRef(v_ref_1223_, v_ref_1233_);
lean_inc_ref(v_inheritedTraceOptions_1243_);
lean_inc(v_cancelTk_x3f_1241_);
lean_inc(v_currMacroScope_1239_);
lean_inc(v_quotContext_1238_);
lean_inc(v_maxHeartbeats_1237_);
lean_inc(v_initHeartbeats_1236_);
lean_inc(v_openDecls_1235_);
lean_inc(v_currNamespace_1234_);
lean_inc(v_maxRecDepth_1232_);
lean_inc(v_currRecDepth_1231_);
lean_inc_ref(v_options_1230_);
lean_inc_ref(v_fileMap_1229_);
lean_inc_ref(v_fileName_1228_);
v___x_1245_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1245_, 0, v_fileName_1228_);
lean_ctor_set(v___x_1245_, 1, v_fileMap_1229_);
lean_ctor_set(v___x_1245_, 2, v_options_1230_);
lean_ctor_set(v___x_1245_, 3, v_currRecDepth_1231_);
lean_ctor_set(v___x_1245_, 4, v_maxRecDepth_1232_);
lean_ctor_set(v___x_1245_, 5, v_ref_1244_);
lean_ctor_set(v___x_1245_, 6, v_currNamespace_1234_);
lean_ctor_set(v___x_1245_, 7, v_openDecls_1235_);
lean_ctor_set(v___x_1245_, 8, v_initHeartbeats_1236_);
lean_ctor_set(v___x_1245_, 9, v_maxHeartbeats_1237_);
lean_ctor_set(v___x_1245_, 10, v_quotContext_1238_);
lean_ctor_set(v___x_1245_, 11, v_currMacroScope_1239_);
lean_ctor_set(v___x_1245_, 12, v_cancelTk_x3f_1241_);
lean_ctor_set(v___x_1245_, 13, v_inheritedTraceOptions_1243_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*14, v_diag_1240_);
lean_ctor_set_uint8(v___x_1245_, sizeof(void*)*14 + 1, v_suppressElabErrors_1242_);
v___x_1246_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(v_msg_1224_, v___x_1245_, v___y_1226_);
lean_dec_ref(v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1247_, lean_object* v_msg_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1247_, v_msg_1248_, v___y_1249_, v___y_1250_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v_ref_1247_);
return v_res_1252_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_1255_ = l_Lean_stringToMessageData(v___x_1254_);
return v___x_1255_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_1258_ = l_Lean_stringToMessageData(v___x_1257_);
return v___x_1258_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_1261_ = l_Lean_stringToMessageData(v___x_1260_);
return v___x_1261_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1264_ = l_Lean_stringToMessageData(v___x_1263_);
return v___x_1264_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1267_ = l_Lean_stringToMessageData(v___x_1266_);
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1270_ = l_Lean_stringToMessageData(v___x_1269_);
return v___x_1270_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1273_ = l_Lean_stringToMessageData(v___x_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1274_, lean_object* v_declHint_1275_, lean_object* v___y_1276_){
_start:
{
lean_object* v___x_1278_; lean_object* v_env_1279_; uint8_t v___x_1280_; 
v___x_1278_ = lean_st_ref_get(v___y_1276_);
v_env_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc_ref(v_env_1279_);
lean_dec(v___x_1278_);
v___x_1280_ = l_Lean_Name_isAnonymous(v_declHint_1275_);
if (v___x_1280_ == 0)
{
uint8_t v_isExporting_1281_; 
v_isExporting_1281_ = lean_ctor_get_uint8(v_env_1279_, sizeof(void*)*8);
if (v_isExporting_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec_ref(v_env_1279_);
lean_dec(v_declHint_1275_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_msg_1274_);
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
lean_inc_ref(v_env_1279_);
v___x_1283_ = l_Lean_Environment_setExporting(v_env_1279_, v___x_1280_);
lean_inc(v_declHint_1275_);
lean_inc_ref(v___x_1283_);
v___x_1284_ = l_Lean_Environment_contains(v___x_1283_, v_declHint_1275_, v_isExporting_1281_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
lean_dec_ref(v___x_1283_);
lean_dec_ref(v_env_1279_);
lean_dec(v_declHint_1275_);
v___x_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1285_, 0, v_msg_1274_);
return v___x_1285_;
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v_c_1291_; lean_object* v___x_1292_; 
v___x_1286_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2);
v___x_1287_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5);
v___x_1288_ = l_Lean_Options_empty;
v___x_1289_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1289_, 0, v___x_1283_);
lean_ctor_set(v___x_1289_, 1, v___x_1286_);
lean_ctor_set(v___x_1289_, 2, v___x_1287_);
lean_ctor_set(v___x_1289_, 3, v___x_1288_);
lean_inc(v_declHint_1275_);
v___x_1290_ = l_Lean_MessageData_ofConstName(v_declHint_1275_, v___x_1280_);
v_c_1291_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1291_, 0, v___x_1289_);
lean_ctor_set(v_c_1291_, 1, v___x_1290_);
v___x_1292_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1279_, v_declHint_1275_);
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_dec_ref(v_env_1279_);
lean_dec(v_declHint_1275_);
v___x_1293_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v_c_1291_);
v___x_1295_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = l_Lean_MessageData_note(v___x_1296_);
v___x_1298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1298_, 0, v_msg_1274_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
return v___x_1299_;
}
else
{
lean_object* v_val_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1335_; 
v_val_1300_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1302_ = v___x_1292_;
v_isShared_1303_ = v_isSharedCheck_1335_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_val_1300_);
lean_dec(v___x_1292_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1335_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v_mod_1307_; uint8_t v___x_1308_; 
v___x_1304_ = lean_box(0);
v___x_1305_ = l_Lean_Environment_header(v_env_1279_);
lean_dec_ref(v_env_1279_);
v___x_1306_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1305_);
v_mod_1307_ = lean_array_get(v___x_1304_, v___x_1306_, v_val_1300_);
lean_dec(v_val_1300_);
lean_dec_ref(v___x_1306_);
v___x_1308_ = l_Lean_isPrivateName(v_declHint_1275_);
lean_dec(v_declHint_1275_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1309_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1310_, 0, v___x_1309_);
lean_ctor_set(v___x_1310_, 1, v_c_1291_);
v___x_1311_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1310_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = l_Lean_MessageData_ofName(v_mod_1307_);
v___x_1314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1312_);
lean_ctor_set(v___x_1314_, 1, v___x_1313_);
v___x_1315_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1314_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
v___x_1317_ = l_Lean_MessageData_note(v___x_1316_);
v___x_1318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1318_, 0, v_msg_1274_);
lean_ctor_set(v___x_1318_, 1, v___x_1317_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set_tag(v___x_1302_, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1318_);
v___x_1320_ = v___x_1302_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
else
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1333_; 
v___x_1322_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
lean_ctor_set(v___x_1323_, 1, v_c_1291_);
v___x_1324_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1323_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
v___x_1326_ = l_Lean_MessageData_ofName(v_mod_1307_);
v___x_1327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1325_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1327_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = l_Lean_MessageData_note(v___x_1329_);
v___x_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_msg_1274_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set_tag(v___x_1302_, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1331_);
v___x_1333_ = v___x_1302_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1336_; 
lean_dec_ref(v_env_1279_);
lean_dec(v_declHint_1275_);
v___x_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1336_, 0, v_msg_1274_);
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1337_, lean_object* v_declHint_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1337_, v_declHint_1338_, v___y_1339_);
lean_dec(v___y_1339_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1342_, lean_object* v_declHint_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v___x_1347_; lean_object* v_a_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1357_; 
v___x_1347_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1342_, v_declHint_1343_, v___y_1345_);
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1357_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_a_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1357_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1352_ = l_Lean_unknownIdentifierMessageTag;
v___x_1353_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v_a_1348_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 0, v___x_1353_);
v___x_1355_ = v___x_1350_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1358_, lean_object* v_declHint_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1358_, v_declHint_1359_, v___y_1360_, v___y_1361_);
lean_dec(v___y_1361_);
lean_dec_ref(v___y_1360_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_ref_1364_, lean_object* v_msg_1365_, lean_object* v_declHint_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; lean_object* v_a_1371_; lean_object* v___x_1372_; 
v___x_1370_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1365_, v_declHint_1366_, v___y_1367_, v___y_1368_);
v_a_1371_ = lean_ctor_get(v___x_1370_, 0);
lean_inc(v_a_1371_);
lean_dec_ref(v___x_1370_);
v___x_1372_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1364_, v_a_1371_, v___y_1367_, v___y_1368_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1373_, lean_object* v_msg_1374_, lean_object* v_declHint_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1373_, v_msg_1374_, v_declHint_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v_ref_1373_);
return v_res_1379_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__0));
v___x_1382_ = l_Lean_stringToMessageData(v___x_1381_);
return v___x_1382_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__2));
v___x_1385_ = l_Lean_stringToMessageData(v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_1386_, lean_object* v_constName_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v___x_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; 
v___x_1391_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_1392_ = 0;
lean_inc(v_constName_1387_);
v___x_1393_ = l_Lean_MessageData_ofConstName(v_constName_1387_, v___x_1392_);
v___x_1394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1391_);
lean_ctor_set(v___x_1394_, 1, v___x_1393_);
v___x_1395_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1396_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1394_);
lean_ctor_set(v___x_1396_, 1, v___x_1395_);
v___x_1397_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1386_, v___x_1396_, v_constName_1387_, v___y_1388_, v___y_1389_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1398_, lean_object* v_constName_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg(v_ref_1398_, v_constName_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v_ref_1398_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg(lean_object* v_constName_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_ref_1408_; lean_object* v___x_1409_; 
v_ref_1408_ = lean_ctor_get(v___y_1405_, 5);
v___x_1409_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg(v_ref_1408_, v_constName_1404_, v___y_1405_, v___y_1406_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg___boxed(lean_object* v_constName_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg(v_constName_1410_, v___y_1411_, v___y_1412_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1(lean_object* v_constName_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v___x_1419_; lean_object* v_env_1420_; uint8_t v___x_1421_; lean_object* v___x_1422_; 
v___x_1419_ = lean_st_ref_get(v___y_1417_);
v_env_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc_ref(v_env_1420_);
lean_dec(v___x_1419_);
v___x_1421_ = 0;
lean_inc(v_constName_1415_);
v___x_1422_ = l_Lean_Environment_find_x3f(v_env_1420_, v_constName_1415_, v___x_1421_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg(v_constName_1415_, v___y_1416_, v___y_1417_);
return v___x_1423_;
}
else
{
lean_object* v_val_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec(v_constName_1415_);
v_val_1424_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1422_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_val_1424_);
lean_dec(v___x_1422_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
lean_ctor_set_tag(v___x_1426_, 0);
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_val_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1___boxed(lean_object* v_constName_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
lean_object* v_res_1436_; 
v_res_1436_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1(v_constName_1432_, v___y_1433_, v___y_1434_);
lean_dec(v___y_1434_);
lean_dec_ref(v___y_1433_);
return v_res_1436_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5(void){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = lean_box(0);
v___x_1446_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__4));
v___x_1447_ = l_Lean_mkConst(v___x_1446_, v___x_1445_);
return v___x_1447_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8(void){
_start:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = lean_box(0);
v___x_1453_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__7));
v___x_1454_ = l_Lean_mkConst(v___x_1453_, v___x_1452_);
return v___x_1454_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__9));
v___x_1457_ = l_Lean_stringToMessageData(v___x_1456_);
return v___x_1457_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_unsigned_to_nat(0u);
v___x_1466_ = l_Lean_Level_ofNat(v___x_1465_);
return v___x_1466_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17(void){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = lean_box(0);
v___x_1468_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16);
v___x_1469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
lean_ctor_set(v___x_1469_, 1, v___x_1467_);
return v___x_1469_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18(void){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1470_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17);
v___x_1471_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16);
v___x_1472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
lean_ctor_set(v___x_1472_, 1, v___x_1470_);
return v___x_1472_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1473_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18);
v___x_1474_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__15));
v___x_1475_ = l_Lean_mkConst(v___x_1474_, v___x_1473_);
return v___x_1475_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21(void){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = lean_box(0);
v___x_1482_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20));
v___x_1483_ = l_Lean_mkConst(v___x_1482_, v___x_1481_);
return v___x_1483_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1490_ = lean_box(0);
v___x_1491_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23));
v___x_1492_ = l_Lean_mkConst(v___x_1491_, v___x_1490_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin(lean_object* v_declName_1500_, lean_object* v_stx_1501_, lean_object* v_addDeclName_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v___y_1507_; lean_object* v___y_1508_; lean_object* v___y_1509_; lean_object* v___y_1510_; lean_object* v___y_1511_; lean_object* v___y_1512_; uint8_t v___y_1533_; lean_object* v_procExpr_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; uint8_t v___y_1543_; lean_object* v___y_1544_; lean_object* v___y_1545_; uint8_t v___y_1557_; lean_object* v___x_1592_; lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1592_ = lean_unsigned_to_nat(1u);
v___x_1593_ = l_Lean_Syntax_getArg(v_stx_1501_, v___x_1592_);
v___x_1594_ = l_Lean_Syntax_isNone(v___x_1593_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1595_ = lean_unsigned_to_nat(0u);
v___x_1596_ = l_Lean_Syntax_getArg(v___x_1593_, v___x_1595_);
lean_dec(v___x_1593_);
v___x_1597_ = l_Lean_Syntax_getKind(v___x_1596_);
v___x_1598_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27));
v___x_1599_ = lean_name_eq(v___x_1597_, v___x_1598_);
lean_dec(v___x_1597_);
v___y_1557_ = v___x_1599_;
goto v___jp_1556_;
}
else
{
lean_dec(v___x_1593_);
v___y_1557_ = v___x_1594_;
goto v___jp_1556_;
}
v___jp_1506_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1513_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__1));
v___x_1514_ = l_Lean_Name_append(v_declName_1500_, v___x_1513_);
v___x_1515_ = l_Lean_Core_mkFreshUserName(v___x_1514_, v___y_1511_, v___y_1509_);
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1516_);
lean_dec_ref(v___x_1515_);
v___x_1517_ = lean_unsigned_to_nat(3u);
v___x_1518_ = lean_mk_empty_array_with_capacity(v___x_1517_);
v___x_1519_ = lean_array_push(v___x_1518_, v___y_1507_);
lean_inc_ref(v___y_1512_);
v___x_1520_ = lean_array_push(v___x_1519_, v___y_1512_);
v___x_1521_ = lean_array_push(v___x_1520_, v___y_1510_);
v___x_1522_ = l_Lean_mkAppN(v___y_1508_, v___x_1521_);
lean_dec_ref(v___x_1521_);
v___x_1523_ = l_Lean_declareBuiltin(v_a_1516_, v___x_1522_, v___y_1511_, v___y_1509_);
return v___x_1523_;
}
else
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1531_; 
lean_dec_ref(v___y_1510_);
lean_dec_ref(v___y_1508_);
lean_dec_ref(v___y_1507_);
v_a_1524_ = lean_ctor_get(v___x_1515_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1526_ = v___x_1515_;
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1515_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1531_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v___x_1529_; 
if (v_isShared_1527_ == 0)
{
v___x_1529_ = v___x_1526_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
v___jp_1532_:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1537_ = lean_box(0);
v___x_1538_ = l_Lean_mkConst(v_addDeclName_1502_, v___x_1537_);
lean_inc(v_declName_1500_);
v___x_1539_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_1500_);
if (v___y_1533_ == 0)
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5);
v___y_1507_ = v___x_1539_;
v___y_1508_ = v___x_1538_;
v___y_1509_ = v___y_1536_;
v___y_1510_ = v_procExpr_1534_;
v___y_1511_ = v___y_1535_;
v___y_1512_ = v___x_1540_;
goto v___jp_1506_;
}
else
{
lean_object* v___x_1541_; 
v___x_1541_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8);
v___y_1507_ = v___x_1539_;
v___y_1508_ = v___x_1538_;
v___y_1509_ = v___y_1536_;
v___y_1510_ = v_procExpr_1534_;
v___y_1511_ = v___y_1535_;
v___y_1512_ = v___x_1541_;
goto v___jp_1506_;
}
}
v___jp_1542_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1555_; 
v___x_1546_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10);
v___x_1547_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(v___x_1546_, v___y_1544_, v___y_1545_);
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1555_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1555_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1555_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1553_; 
if (v_isShared_1551_ == 0)
{
v___x_1553_ = v___x_1550_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_a_1548_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
v___jp_1556_:
{
lean_object* v___x_1558_; 
lean_inc(v_declName_1500_);
v___x_1558_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1(v_declName_1500_, v_a_1503_, v_a_1504_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1560_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref(v___x_1558_);
v___x_1560_ = l_Lean_ConstantInfo_type(v_a_1559_);
lean_dec(v_a_1559_);
if (lean_obj_tag(v___x_1560_) == 4)
{
lean_object* v_declName_1561_; 
v_declName_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_declName_1561_);
lean_dec_ref(v___x_1560_);
if (lean_obj_tag(v_declName_1561_) == 1)
{
lean_object* v_pre_1562_; 
v_pre_1562_ = lean_ctor_get(v_declName_1561_, 0);
lean_inc(v_pre_1562_);
if (lean_obj_tag(v_pre_1562_) == 1)
{
lean_object* v_pre_1563_; 
v_pre_1563_ = lean_ctor_get(v_pre_1562_, 0);
lean_inc(v_pre_1563_);
if (lean_obj_tag(v_pre_1563_) == 1)
{
lean_object* v_pre_1564_; 
v_pre_1564_ = lean_ctor_get(v_pre_1563_, 0);
lean_inc(v_pre_1564_);
if (lean_obj_tag(v_pre_1564_) == 1)
{
lean_object* v_pre_1565_; 
v_pre_1565_ = lean_ctor_get(v_pre_1564_, 0);
if (lean_obj_tag(v_pre_1565_) == 0)
{
lean_object* v_str_1566_; lean_object* v_str_1567_; lean_object* v_str_1568_; lean_object* v_str_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v_str_1566_ = lean_ctor_get(v_declName_1561_, 1);
lean_inc_ref(v_str_1566_);
lean_dec_ref(v_declName_1561_);
v_str_1567_ = lean_ctor_get(v_pre_1562_, 1);
lean_inc_ref(v_str_1567_);
lean_dec_ref(v_pre_1562_);
v_str_1568_ = lean_ctor_get(v_pre_1563_, 1);
lean_inc_ref(v_str_1568_);
lean_dec_ref(v_pre_1563_);
v_str_1569_ = lean_ctor_get(v_pre_1564_, 1);
lean_inc_ref(v_str_1569_);
lean_dec_ref(v_pre_1564_);
v___x_1570_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_1571_ = lean_string_dec_eq(v_str_1569_, v___x_1570_);
lean_dec_ref(v_str_1569_);
if (v___x_1571_ == 0)
{
lean_dec_ref(v_str_1568_);
lean_dec_ref(v_str_1567_);
lean_dec_ref(v_str_1566_);
lean_dec(v_addDeclName_1502_);
lean_dec(v_declName_1500_);
v___y_1543_ = v___y_1557_;
v___y_1544_ = v_a_1503_;
v___y_1545_ = v_a_1504_;
goto v___jp_1542_;
}
else
{
lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_1573_ = lean_string_dec_eq(v_str_1568_, v___x_1572_);
lean_dec_ref(v_str_1568_);
if (v___x_1573_ == 0)
{
lean_dec_ref(v_str_1567_);
lean_dec_ref(v_str_1566_);
lean_dec(v_addDeclName_1502_);
lean_dec(v_declName_1500_);
v___y_1543_ = v___y_1557_;
v___y_1544_ = v_a_1503_;
v___y_1545_ = v_a_1504_;
goto v___jp_1542_;
}
else
{
lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1574_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__11));
v___x_1575_ = lean_string_dec_eq(v_str_1567_, v___x_1574_);
lean_dec_ref(v_str_1567_);
if (v___x_1575_ == 0)
{
lean_dec_ref(v_str_1566_);
lean_dec(v_addDeclName_1502_);
lean_dec(v_declName_1500_);
v___y_1543_ = v___y_1557_;
v___y_1544_ = v_a_1503_;
v___y_1545_ = v_a_1504_;
goto v___jp_1542_;
}
else
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__12));
v___x_1577_ = lean_string_dec_eq(v_str_1566_, v___x_1576_);
lean_dec_ref(v_str_1566_);
if (v___x_1577_ == 0)
{
lean_dec(v_addDeclName_1502_);
lean_dec(v_declName_1500_);
v___y_1543_ = v___y_1557_;
v___y_1544_ = v_a_1503_;
v___y_1545_ = v_a_1504_;
goto v___jp_1542_;
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1578_ = lean_box(0);
v___x_1579_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19);
v___x_1580_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21);
v___x_1581_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24);
lean_inc(v_declName_1500_);
v___x_1582_ = l_Lean_mkConst(v_declName_1500_, v___x_1578_);
v___x_1583_ = l_Lean_mkApp3(v___x_1579_, v___x_1580_, v___x_1581_, v___x_1582_);
v___y_1533_ = v___y_1557_;
v_procExpr_1534_ = v___x_1583_;
v___y_1535_ = v_a_1503_;
v___y_1536_ = v_a_1504_;
goto v___jp_1532_;
}
}
}
}
}
else
{
lean_dec_ref(v_pre_1564_);
lean_dec_ref(v_pre_1563_);
lean_dec_ref(v_pre_1562_);
lean_dec_ref(v_declName_1561_);
lean_dec(v_addDeclName_1502_);
lean_dec(v_declName_1500_);
v___y_1543_ = v___y_1557_;
v___y_1544_ = v_a_1503_;
v___y_1545_ = v_a_1504_;
goto v___jp_1542_;
}
}
else
{
lean_dec_ref(v_pre_1563_);
lean_dec(v_pre_1564_);
lean_dec_ref(v_pre_1562_);
lean_dec_ref(v_declName_1561_);
lean_dec(v_addDeclName_1502_);
lean_dec(v_declName_1500_);
v___y_1543_ = v___y_1557_;
v___y_1544_ = v_a_1503_;
v___y_1545_ = v_a_1504_;
goto v___jp_1542_;
}
}
else
{
lean_dec_ref(v_pre_1562_);
lean_dec(v_pre_1563_);
lean_dec_ref(v_declName_1561_);
lean_dec(v_addDeclName_1502_);
lean_dec(v_declName_1500_);
v___y_1543_ = v___y_1557_;
v___y_1544_ = v_a_1503_;
v___y_1545_ = v_a_1504_;
goto v___jp_1542_;
}
}
else
{
lean_dec(v_pre_1562_);
lean_dec_ref(v_declName_1561_);
lean_dec(v_addDeclName_1502_);
lean_dec(v_declName_1500_);
v___y_1543_ = v___y_1557_;
v___y_1544_ = v_a_1503_;
v___y_1545_ = v_a_1504_;
goto v___jp_1542_;
}
}
else
{
lean_dec(v_declName_1561_);
lean_dec(v_addDeclName_1502_);
lean_dec(v_declName_1500_);
v___y_1543_ = v___y_1557_;
v___y_1544_ = v_a_1503_;
v___y_1545_ = v_a_1504_;
goto v___jp_1542_;
}
}
else
{
lean_dec_ref(v___x_1560_);
lean_dec(v_addDeclName_1502_);
lean_dec(v_declName_1500_);
v___y_1543_ = v___y_1557_;
v___y_1544_ = v_a_1503_;
v___y_1545_ = v_a_1504_;
goto v___jp_1542_;
}
}
else
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1591_; 
lean_dec(v_addDeclName_1502_);
lean_dec(v_declName_1500_);
v_a_1584_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1586_ = v___x_1558_;
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1558_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1591_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1589_; 
if (v_isShared_1587_ == 0)
{
v___x_1589_ = v___x_1586_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_a_1584_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___boxed(lean_object* v_declName_1600_, lean_object* v_stx_1601_, lean_object* v_addDeclName_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_){
_start:
{
lean_object* v_res_1606_; 
v_res_1606_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin(v_declName_1600_, v_stx_1601_, v_addDeclName_1602_, v_a_1603_, v_a_1604_);
lean_dec(v_a_1604_);
lean_dec_ref(v_a_1603_);
lean_dec(v_stx_1601_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0(lean_object* v_00_u03b1_1607_, lean_object* v_msg_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(v_msg_1608_, v___y_1609_, v___y_1610_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___boxed(lean_object* v_00_u03b1_1613_, lean_object* v_msg_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0(v_00_u03b1_1613_, v_msg_1614_, v___y_1615_, v___y_1616_);
lean_dec(v___y_1616_);
lean_dec_ref(v___y_1615_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2(lean_object* v_00_u03b1_1619_, lean_object* v_constName_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg(v_constName_1620_, v___y_1621_, v___y_1622_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1625_, lean_object* v_constName_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2(v_00_u03b1_1625_, v_constName_1626_, v___y_1627_, v___y_1628_);
lean_dec(v___y_1628_);
lean_dec_ref(v___y_1627_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_1631_, lean_object* v_ref_1632_, lean_object* v_constName_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg(v_ref_1632_, v_constName_1633_, v___y_1634_, v___y_1635_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1638_, lean_object* v_ref_1639_, lean_object* v_constName_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3(v_00_u03b1_1638_, v_ref_1639_, v_constName_1640_, v___y_1641_, v___y_1642_);
lean_dec(v___y_1642_);
lean_dec_ref(v___y_1641_);
lean_dec(v_ref_1639_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1645_, lean_object* v_ref_1646_, lean_object* v_msg_1647_, lean_object* v_declHint_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1646_, v_msg_1647_, v_declHint_1648_, v___y_1649_, v___y_1650_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1653_, lean_object* v_ref_1654_, lean_object* v_msg_1655_, lean_object* v_declHint_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_1653_, v_ref_1654_, v_msg_1655_, v_declHint_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
lean_dec(v_ref_1654_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_1661_, lean_object* v_declHint_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1661_, v_declHint_1662_, v___y_1664_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1667_, lean_object* v_declHint_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(v_msg_1667_, v_declHint_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
lean_dec_ref(v___y_1669_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b1_1673_, lean_object* v_ref_1674_, lean_object* v_msg_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1674_, v_msg_1675_, v___y_1676_, v___y_1677_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1680_, lean_object* v_ref_1681_, lean_object* v_msg_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6(v_00_u03b1_1680_, v_ref_1681_, v_msg_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v_ref_1681_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr(lean_object* v_declName_1687_, uint8_t v_post_1688_, lean_object* v_proc_1689_){
_start:
{
lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1691_ = l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef;
v___x_1692_ = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(v___x_1691_, v_declName_1687_, v_post_1688_, v_proc_1689_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr___boxed(lean_object* v_declName_1693_, lean_object* v_post_1694_, lean_object* v_proc_1695_, lean_object* v_a_1696_){
_start:
{
uint8_t v_post_boxed_1697_; lean_object* v_res_1698_; 
v_post_boxed_1697_ = lean_unbox(v_post_1694_);
v_res_1698_ = l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr(v_declName_1693_, v_post_boxed_1697_, v_proc_1695_);
return v_res_1698_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_));
v___x_1701_ = l_Lean_stringToMessageData(v___x_1700_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(lean_object* v_x_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_);
v___x_1707_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(v___x_1706_, v___y_1703_, v___y_1704_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed(lean_object* v_x_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(v_x_1708_, v___y_1709_, v___y_1710_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v_x_1708_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(lean_object* v___x_1714_, lean_object* v___x_1715_, lean_object* v___x_1716_, lean_object* v___x_1717_, lean_object* v___x_1718_, lean_object* v_declName_1719_, lean_object* v_stx_1720_, uint8_t v_x_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_));
v___x_1726_ = l_Lean_Name_mkStr6(v___x_1714_, v___x_1715_, v___x_1716_, v___x_1717_, v___x_1718_, v___x_1725_);
v___x_1727_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin(v_declName_1719_, v_stx_1720_, v___x_1726_, v___y_1722_, v___y_1723_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed(lean_object* v___x_1728_, lean_object* v___x_1729_, lean_object* v___x_1730_, lean_object* v___x_1731_, lean_object* v___x_1732_, lean_object* v_declName_1733_, lean_object* v_stx_1734_, lean_object* v_x_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
uint8_t v_x_164__boxed_1739_; lean_object* v_res_1740_; 
v_x_164__boxed_1739_ = lean_unbox(v_x_1735_);
v_res_1740_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(v___x_1728_, v___x_1729_, v___x_1730_, v___x_1731_, v___x_1732_, v_declName_1733_, v_stx_1734_, v_x_164__boxed_1739_, v___y_1736_, v___y_1737_);
lean_dec(v___y_1737_);
lean_dec_ref(v___y_1736_);
lean_dec(v_stx_1734_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1774_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_));
v___x_1775_ = l_Lean_registerBuiltinAttribute(v___x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed(lean_object* v_a_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_();
return v_res_1777_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3575118154____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_BVDecide_Frontend_sat_solver = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_sat_solver);
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeExt);
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_BVDecide_Frontend_intToBitVecExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_intToBitVecExt);
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef);
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeSimprocExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeSimprocExt);
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Syntax(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
