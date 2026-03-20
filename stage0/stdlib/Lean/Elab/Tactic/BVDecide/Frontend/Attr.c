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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
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
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
lean_object* l_Lean_instToExprName___private__1(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg___closed__0;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__21_value;
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v_name_124_);
v___x_134_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_134_, 0, v_name_124_);
lean_ctor_set(v___x_134_, 1, v_ref_126_);
lean_ctor_set(v___x_134_, 2, v___x_133_);
lean_ctor_set(v___x_134_, 3, v_descr_129_);
lean_inc(v_name_124_);
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
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__6___redArg(lean_object* v_a_228_, lean_object* v_x_229_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_a_237_, lean_object* v_x_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__6___redArg(v_a_237_, v_x_238_);
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
v___x_260_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__6___redArg(v_a_243_, v___x_259_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__4(lean_object* v_msgData_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v___x_272_; lean_object* v_env_273_; lean_object* v___x_274_; lean_object* v_mctx_275_; lean_object* v_lctx_276_; lean_object* v_options_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_272_ = lean_st_ref_get(v___y_270_);
v_env_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc_ref(v_env_273_);
lean_dec(v___x_272_);
v___x_274_ = lean_st_ref_get(v___y_268_);
v_mctx_275_ = lean_ctor_get(v___x_274_, 0);
lean_inc_ref(v_mctx_275_);
lean_dec(v___x_274_);
v_lctx_276_ = lean_ctor_get(v___y_267_, 2);
v_options_277_ = lean_ctor_get(v___y_269_, 2);
lean_inc_ref(v_options_277_);
lean_inc_ref(v_lctx_276_);
v___x_278_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_278_, 0, v_env_273_);
lean_ctor_set(v___x_278_, 1, v_mctx_275_);
lean_ctor_set(v___x_278_, 2, v_lctx_276_);
lean_ctor_set(v___x_278_, 3, v_options_277_);
v___x_279_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v_msgData_266_);
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__4___boxed(lean_object* v_msgData_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__4(v_msgData_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
return v_res_287_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_288_; double v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = lean_float_of_nat(v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg(lean_object* v_cls_292_, lean_object* v_msg_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v_ref_299_; lean_object* v___x_300_; lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_345_; 
v_ref_299_ = lean_ctor_get(v___y_296_, 5);
v___x_300_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__4(v_msg_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
v_a_301_ = lean_ctor_get(v___x_300_, 0);
v_isSharedCheck_345_ = !lean_is_exclusive(v___x_300_);
if (v_isSharedCheck_345_ == 0)
{
v___x_303_ = v___x_300_;
v_isShared_304_ = v_isSharedCheck_345_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_345_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_305_; lean_object* v_traceState_306_; lean_object* v_env_307_; lean_object* v_nextMacroScope_308_; lean_object* v_ngen_309_; lean_object* v_auxDeclNGen_310_; lean_object* v_cache_311_; lean_object* v_messages_312_; lean_object* v_infoState_313_; lean_object* v_snapshotTasks_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_344_; 
v___x_305_ = lean_st_ref_take(v___y_297_);
v_traceState_306_ = lean_ctor_get(v___x_305_, 4);
v_env_307_ = lean_ctor_get(v___x_305_, 0);
v_nextMacroScope_308_ = lean_ctor_get(v___x_305_, 1);
v_ngen_309_ = lean_ctor_get(v___x_305_, 2);
v_auxDeclNGen_310_ = lean_ctor_get(v___x_305_, 3);
v_cache_311_ = lean_ctor_get(v___x_305_, 5);
v_messages_312_ = lean_ctor_get(v___x_305_, 6);
v_infoState_313_ = lean_ctor_get(v___x_305_, 7);
v_snapshotTasks_314_ = lean_ctor_get(v___x_305_, 8);
v_isSharedCheck_344_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_344_ == 0)
{
v___x_316_ = v___x_305_;
v_isShared_317_ = v_isSharedCheck_344_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_snapshotTasks_314_);
lean_inc(v_infoState_313_);
lean_inc(v_messages_312_);
lean_inc(v_cache_311_);
lean_inc(v_traceState_306_);
lean_inc(v_auxDeclNGen_310_);
lean_inc(v_ngen_309_);
lean_inc(v_nextMacroScope_308_);
lean_inc(v_env_307_);
lean_dec(v___x_305_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_344_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
uint64_t v_tid_318_; lean_object* v_traces_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_343_; 
v_tid_318_ = lean_ctor_get_uint64(v_traceState_306_, sizeof(void*)*1);
v_traces_319_ = lean_ctor_get(v_traceState_306_, 0);
v_isSharedCheck_343_ = !lean_is_exclusive(v_traceState_306_);
if (v_isSharedCheck_343_ == 0)
{
v___x_321_ = v_traceState_306_;
v_isShared_322_ = v_isSharedCheck_343_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_traces_319_);
lean_dec(v_traceState_306_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_343_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; double v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_323_ = lean_box(0);
v___x_324_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_325_ = 0;
v___x_326_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_));
v___x_327_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_327_, 0, v_cls_292_);
lean_ctor_set(v___x_327_, 1, v___x_323_);
lean_ctor_set(v___x_327_, 2, v___x_326_);
lean_ctor_set_float(v___x_327_, sizeof(void*)*3, v___x_324_);
lean_ctor_set_float(v___x_327_, sizeof(void*)*3 + 8, v___x_324_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*3 + 16, v___x_325_);
v___x_328_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg___closed__1));
v___x_329_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_329_, 0, v___x_327_);
lean_ctor_set(v___x_329_, 1, v_a_301_);
lean_ctor_set(v___x_329_, 2, v___x_328_);
lean_inc(v_ref_299_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v_ref_299_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = l_Lean_PersistentArray_push___redArg(v_traces_319_, v___x_330_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_331_);
v___x_333_ = v___x_321_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_331_);
lean_ctor_set_uint64(v_reuseFailAlloc_342_, sizeof(void*)*1, v_tid_318_);
v___x_333_ = v_reuseFailAlloc_342_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_335_; 
if (v_isShared_317_ == 0)
{
lean_ctor_set(v___x_316_, 4, v___x_333_);
v___x_335_ = v___x_316_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_env_307_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_nextMacroScope_308_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v_ngen_309_);
lean_ctor_set(v_reuseFailAlloc_341_, 3, v_auxDeclNGen_310_);
lean_ctor_set(v_reuseFailAlloc_341_, 4, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_341_, 5, v_cache_311_);
lean_ctor_set(v_reuseFailAlloc_341_, 6, v_messages_312_);
lean_ctor_set(v_reuseFailAlloc_341_, 7, v_infoState_313_);
lean_ctor_set(v_reuseFailAlloc_341_, 8, v_snapshotTasks_314_);
v___x_335_ = v_reuseFailAlloc_341_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_339_; 
v___x_336_ = lean_st_ref_set(v___y_297_, v___x_335_);
v___x_337_ = lean_box(0);
if (v_isShared_304_ == 0)
{
lean_ctor_set(v___x_303_, 0, v___x_337_);
v___x_339_ = v___x_303_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_337_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
return v___x_339_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_cls_346_, lean_object* v_msg_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg(v_cls_346_, v_msg_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_);
lean_dec(v___y_351_);
lean_dec_ref(v___y_350_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
return v_res_353_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(lean_object* v_keys_354_, lean_object* v_i_355_, lean_object* v_k_356_){
_start:
{
lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_357_ = lean_array_get_size(v_keys_354_);
v___x_358_ = lean_nat_dec_lt(v_i_355_, v___x_357_);
if (v___x_358_ == 0)
{
lean_dec(v_i_355_);
return v___x_358_;
}
else
{
lean_object* v_k_x27_359_; uint8_t v___x_360_; 
v_k_x27_359_ = lean_array_fget_borrowed(v_keys_354_, v_i_355_);
v___x_360_ = l_Lean_instBEqExtraModUse_beq(v_k_356_, v_k_x27_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = lean_unsigned_to_nat(1u);
v___x_362_ = lean_nat_add(v_i_355_, v___x_361_);
lean_dec(v_i_355_);
v_i_355_ = v___x_362_;
goto _start;
}
else
{
lean_dec(v_i_355_);
return v___x_360_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_keys_364_, lean_object* v_i_365_, lean_object* v_k_366_){
_start:
{
uint8_t v_res_367_; lean_object* v_r_368_; 
v_res_367_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_keys_364_, v_i_365_, v_k_366_);
lean_dec_ref(v_k_366_);
lean_dec_ref(v_keys_364_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0(void){
_start:
{
size_t v___x_369_; size_t v___x_370_; size_t v___x_371_; 
v___x_369_ = ((size_t)5ULL);
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_shift_left(v___x_370_, v___x_369_);
return v___x_371_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_372_; size_t v___x_373_; size_t v___x_374_; 
v___x_372_ = ((size_t)1ULL);
v___x_373_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__0);
v___x_374_ = lean_usize_sub(v___x_373_, v___x_372_);
return v___x_374_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_x_375_, size_t v_x_376_, lean_object* v_x_377_){
_start:
{
if (lean_obj_tag(v_x_375_) == 0)
{
lean_object* v_es_378_; lean_object* v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; lean_object* v_j_383_; lean_object* v___x_384_; 
v_es_378_ = lean_ctor_get(v_x_375_, 0);
lean_inc_ref(v_es_378_);
lean_dec_ref(v_x_375_);
v___x_379_ = lean_box(2);
v___x_380_ = ((size_t)5ULL);
v___x_381_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___closed__1);
v___x_382_ = lean_usize_land(v_x_376_, v___x_381_);
v_j_383_ = lean_usize_to_nat(v___x_382_);
v___x_384_ = lean_array_get(v___x_379_, v_es_378_, v_j_383_);
lean_dec(v_j_383_);
lean_dec_ref(v_es_378_);
switch(lean_obj_tag(v___x_384_))
{
case 0:
{
lean_object* v_key_385_; uint8_t v___x_386_; 
v_key_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_key_385_);
lean_dec_ref(v___x_384_);
v___x_386_ = l_Lean_instBEqExtraModUse_beq(v_x_377_, v_key_385_);
lean_dec(v_key_385_);
return v___x_386_;
}
case 1:
{
lean_object* v_node_387_; size_t v___x_388_; 
v_node_387_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_node_387_);
lean_dec_ref(v___x_384_);
v___x_388_ = lean_usize_shift_right(v_x_376_, v___x_380_);
v_x_375_ = v_node_387_;
v_x_376_ = v___x_388_;
goto _start;
}
default: 
{
uint8_t v___x_390_; 
v___x_390_ = 0;
return v___x_390_;
}
}
}
else
{
lean_object* v_ks_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v_ks_391_ = lean_ctor_get(v_x_375_, 0);
lean_inc_ref(v_ks_391_);
lean_dec_ref(v_x_375_);
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_ks_391_, v___x_392_, v_x_377_);
lean_dec_ref(v_ks_391_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_x_394_, lean_object* v_x_395_, lean_object* v_x_396_){
_start:
{
size_t v_x_12461__boxed_397_; uint8_t v_res_398_; lean_object* v_r_399_; 
v_x_12461__boxed_397_ = lean_unbox_usize(v_x_395_);
lean_dec(v_x_395_);
v_res_398_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg(v_x_394_, v_x_12461__boxed_397_, v_x_396_);
lean_dec_ref(v_x_396_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_x_400_, lean_object* v_x_401_){
_start:
{
uint64_t v___x_402_; size_t v___x_403_; uint8_t v___x_404_; 
v___x_402_ = l_Lean_instHashableExtraModUse_hash(v_x_401_);
v___x_403_ = lean_uint64_to_usize(v___x_402_);
v___x_404_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg(v_x_400_, v___x_403_, v_x_401_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_405_, lean_object* v_x_406_){
_start:
{
uint8_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___redArg(v_x_405_, v_x_406_);
lean_dec_ref(v_x_406_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_412_, lean_object* v___y_413_){
_start:
{
lean_object* v_options_415_; uint8_t v_hasTrace_416_; 
v_options_415_ = lean_ctor_get(v___y_413_, 2);
v_hasTrace_416_ = lean_ctor_get_uint8(v_options_415_, sizeof(void*)*1);
if (v_hasTrace_416_ == 0)
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec(v_cls_412_);
v___x_417_ = lean_box(v_hasTrace_416_);
v___x_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
return v___x_418_;
}
else
{
lean_object* v_inheritedTraceOptions_419_; lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v_inheritedTraceOptions_419_ = lean_ctor_get(v___y_413_, 13);
v___x_420_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___closed__1));
v___x_421_ = l_Lean_Name_append(v___x_420_, v_cls_412_);
v___x_422_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_419_, v_options_415_, v___x_421_);
lean_dec(v___x_421_);
v___x_423_ = lean_box(v___x_422_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg(v_cls_425_, v___y_426_);
lean_dec_ref(v___y_426_);
return v_res_428_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_431_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__1));
v___x_432_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__0));
v___x_433_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_432_, v___x_431_);
return v___x_433_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_434_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__3);
v___x_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
return v___x_436_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__4);
v___x_440_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
lean_ctor_set(v___x_440_, 2, v___x_439_);
lean_ctor_set(v___x_440_, 3, v___x_439_);
lean_ctor_set(v___x_440_, 4, v___x_439_);
lean_ctor_set(v___x_440_, 5, v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__9));
v___x_446_ = l_Lean_stringToMessageData(v___x_445_);
return v___x_446_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__11));
v___x_449_ = l_Lean_stringToMessageData(v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1794396972____hygCtx___hyg_4_));
v___x_451_ = l_Lean_stringToMessageData(v___x_450_);
return v___x_451_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__15(void){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__14));
v___x_454_ = l_Lean_stringToMessageData(v___x_453_);
return v___x_454_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__17(void){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__16));
v___x_457_ = l_Lean_stringToMessageData(v___x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0(lean_object* v_mod_462_, uint8_t v_isMeta_463_, lean_object* v_hint_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___x_472_; lean_object* v_env_473_; uint8_t v_isExporting_474_; lean_object* v___x_475_; lean_object* v_env_476_; lean_object* v___x_477_; lean_object* v_entry_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___y_483_; lean_object* v___y_484_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_472_ = lean_st_ref_get(v___y_470_);
v_env_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc_ref(v_env_473_);
lean_dec(v___x_472_);
v_isExporting_474_ = lean_ctor_get_uint8(v_env_473_, sizeof(void*)*8);
lean_dec_ref(v_env_473_);
v___x_475_ = lean_st_ref_get(v___y_470_);
v_env_476_ = lean_ctor_get(v___x_475_, 0);
lean_inc_ref(v_env_476_);
lean_dec(v___x_475_);
v___x_477_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__2);
lean_inc(v_mod_462_);
v_entry_478_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_478_, 0, v_mod_462_);
lean_ctor_set_uint8(v_entry_478_, sizeof(void*)*1, v_isExporting_474_);
lean_ctor_set_uint8(v_entry_478_, sizeof(void*)*1 + 1, v_isMeta_463_);
v___x_479_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_480_ = lean_box(1);
v___x_481_ = lean_box(0);
v___x_524_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_477_, v___x_479_, v_env_476_, v___x_480_, v___x_481_);
v___x_525_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___redArg(v___x_524_, v_entry_478_);
if (v___x_525_ == 0)
{
lean_object* v_cls_526_; lean_object* v___x_527_; lean_object* v_a_528_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_535_; lean_object* v___y_536_; uint8_t v___x_548_; 
v_cls_526_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__8));
v___x_527_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg(v_cls_526_, v___y_469_);
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
lean_dec_ref(v___x_527_);
v___x_548_ = lean_unbox(v_a_528_);
lean_dec(v_a_528_);
if (v___x_548_ == 0)
{
lean_dec(v_hint_464_);
lean_dec(v_mod_462_);
v___y_483_ = v___y_468_;
v___y_484_ = v___y_470_;
goto v___jp_482_;
}
else
{
lean_object* v___x_549_; lean_object* v___y_551_; 
v___x_549_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__15);
if (v_isExporting_474_ == 0)
{
lean_object* v___x_558_; 
v___x_558_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__20));
v___y_551_ = v___x_558_;
goto v___jp_550_;
}
else
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__21));
v___y_551_ = v___x_559_;
goto v___jp_550_;
}
v___jp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_552_ = l_Lean_stringToMessageData(v___y_551_);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_549_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__17);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
if (v_isMeta_463_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__18));
v___y_535_ = v___x_555_;
v___y_536_ = v___x_556_;
goto v___jp_534_;
}
else
{
lean_object* v___x_557_; 
v___x_557_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__19));
v___y_535_ = v___x_555_;
v___y_536_ = v___x_557_;
goto v___jp_534_;
}
}
}
v___jp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_532_, 0, v___y_530_);
lean_ctor_set(v___x_532_, 1, v___y_531_);
v___x_533_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg(v_cls_526_, v___x_532_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_533_) == 0)
{
lean_dec_ref(v___x_533_);
v___y_483_ = v___y_468_;
v___y_484_ = v___y_470_;
goto v___jp_482_;
}
else
{
lean_dec_ref(v_entry_478_);
return v___x_533_;
}
}
v___jp_534_:
{
lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_537_ = l_Lean_stringToMessageData(v___y_536_);
v___x_538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_538_, 0, v___y_535_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
v___x_539_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__10);
v___x_540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = l_Lean_MessageData_ofName(v_mod_462_);
v___x_542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_540_);
lean_ctor_set(v___x_542_, 1, v___x_541_);
v___x_543_ = l_Lean_Name_isAnonymous(v_hint_464_);
if (v___x_543_ == 0)
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__12);
v___x_545_ = l_Lean_MessageData_ofName(v_hint_464_);
v___x_546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___y_530_ = v___x_542_;
v___y_531_ = v___x_546_;
goto v___jp_529_;
}
else
{
lean_object* v___x_547_; 
lean_dec(v_hint_464_);
v___x_547_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__13);
v___y_530_ = v___x_542_;
v___y_531_ = v___x_547_;
goto v___jp_529_;
}
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec_ref(v_entry_478_);
lean_dec(v_hint_464_);
lean_dec(v_mod_462_);
v___x_560_ = lean_box(0);
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
return v___x_561_;
}
v___jp_482_:
{
lean_object* v___x_485_; lean_object* v_toEnvExtension_486_; lean_object* v_env_487_; lean_object* v_nextMacroScope_488_; lean_object* v_ngen_489_; lean_object* v_auxDeclNGen_490_; lean_object* v_traceState_491_; lean_object* v_messages_492_; lean_object* v_infoState_493_; lean_object* v_snapshotTasks_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_522_; 
v___x_485_ = lean_st_ref_take(v___y_484_);
v_toEnvExtension_486_ = lean_ctor_get(v___x_479_, 0);
lean_inc_ref(v_toEnvExtension_486_);
v_env_487_ = lean_ctor_get(v___x_485_, 0);
v_nextMacroScope_488_ = lean_ctor_get(v___x_485_, 1);
v_ngen_489_ = lean_ctor_get(v___x_485_, 2);
v_auxDeclNGen_490_ = lean_ctor_get(v___x_485_, 3);
v_traceState_491_ = lean_ctor_get(v___x_485_, 4);
v_messages_492_ = lean_ctor_get(v___x_485_, 6);
v_infoState_493_ = lean_ctor_get(v___x_485_, 7);
v_snapshotTasks_494_ = lean_ctor_get(v___x_485_, 8);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_485_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v___x_485_, 5);
lean_dec(v_unused_523_);
v___x_496_ = v___x_485_;
v_isShared_497_ = v_isSharedCheck_522_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_snapshotTasks_494_);
lean_inc(v_infoState_493_);
lean_inc(v_messages_492_);
lean_inc(v_traceState_491_);
lean_inc(v_auxDeclNGen_490_);
lean_inc(v_ngen_489_);
lean_inc(v_nextMacroScope_488_);
lean_inc(v_env_487_);
lean_dec(v___x_485_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_522_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v_asyncMode_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v_asyncMode_498_ = lean_ctor_get(v_toEnvExtension_486_, 2);
lean_inc(v_asyncMode_498_);
lean_dec_ref(v_toEnvExtension_486_);
v___x_499_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_479_, v_env_487_, v_entry_478_, v_asyncMode_498_, v___x_481_);
lean_dec(v_asyncMode_498_);
v___x_500_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__5);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 5, v___x_500_);
lean_ctor_set(v___x_496_, 0, v___x_499_);
v___x_502_ = v___x_496_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_499_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_nextMacroScope_488_);
lean_ctor_set(v_reuseFailAlloc_521_, 2, v_ngen_489_);
lean_ctor_set(v_reuseFailAlloc_521_, 3, v_auxDeclNGen_490_);
lean_ctor_set(v_reuseFailAlloc_521_, 4, v_traceState_491_);
lean_ctor_set(v_reuseFailAlloc_521_, 5, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_521_, 6, v_messages_492_);
lean_ctor_set(v_reuseFailAlloc_521_, 7, v_infoState_493_);
lean_ctor_set(v_reuseFailAlloc_521_, 8, v_snapshotTasks_494_);
v___x_502_ = v_reuseFailAlloc_521_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v_mctx_505_; lean_object* v_zetaDeltaFVarIds_506_; lean_object* v_postponed_507_; lean_object* v_diag_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_519_; 
v___x_503_ = lean_st_ref_set(v___y_484_, v___x_502_);
v___x_504_ = lean_st_ref_take(v___y_483_);
v_mctx_505_ = lean_ctor_get(v___x_504_, 0);
v_zetaDeltaFVarIds_506_ = lean_ctor_get(v___x_504_, 2);
v_postponed_507_ = lean_ctor_get(v___x_504_, 3);
v_diag_508_ = lean_ctor_get(v___x_504_, 4);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; 
v_unused_520_ = lean_ctor_get(v___x_504_, 1);
lean_dec(v_unused_520_);
v___x_510_ = v___x_504_;
v_isShared_511_ = v_isSharedCheck_519_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_diag_508_);
lean_inc(v_postponed_507_);
lean_inc(v_zetaDeltaFVarIds_506_);
lean_inc(v_mctx_505_);
lean_dec(v___x_504_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_519_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_512_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___closed__6);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v___x_512_);
v___x_514_ = v___x_510_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_mctx_505_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_518_, 2, v_zetaDeltaFVarIds_506_);
lean_ctor_set(v_reuseFailAlloc_518_, 3, v_postponed_507_);
lean_ctor_set(v_reuseFailAlloc_518_, 4, v_diag_508_);
v___x_514_ = v_reuseFailAlloc_518_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_st_ref_set(v___y_483_, v___x_514_);
v___x_516_ = lean_box(0);
v___x_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
return v___x_517_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0___boxed(lean_object* v_mod_562_, lean_object* v_isMeta_563_, lean_object* v_hint_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
uint8_t v_isMeta_boxed_572_; lean_object* v_res_573_; 
v_isMeta_boxed_572_ = lean_unbox(v_isMeta_563_);
v_res_573_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0(v_mod_562_, v_isMeta_boxed_572_, v_hint_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__1(lean_object* v___x_574_, lean_object* v_declName_575_, lean_object* v_as_576_, size_t v_sz_577_, size_t v_i_578_, lean_object* v_b_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
uint8_t v___x_587_; 
v___x_587_ = lean_usize_dec_lt(v_i_578_, v_sz_577_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; 
lean_dec(v_declName_575_);
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v_b_579_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; lean_object* v_modules_590_; lean_object* v___x_591_; lean_object* v_a_592_; lean_object* v___x_593_; lean_object* v_toImport_594_; lean_object* v_module_595_; uint8_t v___x_596_; lean_object* v___x_597_; 
v___x_589_ = l_Lean_Environment_header(v___x_574_);
v_modules_590_ = lean_ctor_get(v___x_589_, 3);
lean_inc_ref(v_modules_590_);
lean_dec_ref(v___x_589_);
v___x_591_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_592_ = lean_array_uget_borrowed(v_as_576_, v_i_578_);
v___x_593_ = lean_array_get(v___x_591_, v_modules_590_, v_a_592_);
lean_dec_ref(v_modules_590_);
v_toImport_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc_ref(v_toImport_594_);
lean_dec(v___x_593_);
v_module_595_ = lean_ctor_get(v_toImport_594_, 0);
lean_inc(v_module_595_);
lean_dec_ref(v_toImport_594_);
v___x_596_ = 0;
lean_inc(v_declName_575_);
v___x_597_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0(v_module_595_, v___x_596_, v_declName_575_, v___y_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v___x_598_; size_t v___x_599_; size_t v___x_600_; 
lean_dec_ref(v___x_597_);
v___x_598_ = lean_box(0);
v___x_599_ = ((size_t)1ULL);
v___x_600_ = lean_usize_add(v_i_578_, v___x_599_);
v_i_578_ = v___x_600_;
v_b_579_ = v___x_598_;
goto _start;
}
else
{
lean_dec(v_declName_575_);
return v___x_597_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__1___boxed(lean_object* v___x_602_, lean_object* v_declName_603_, lean_object* v_as_604_, lean_object* v_sz_605_, lean_object* v_i_606_, lean_object* v_b_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
size_t v_sz_boxed_615_; size_t v_i_boxed_616_; lean_object* v_res_617_; 
v_sz_boxed_615_ = lean_unbox_usize(v_sz_605_);
lean_dec(v_sz_605_);
v_i_boxed_616_ = lean_unbox_usize(v_i_606_);
lean_dec(v_i_606_);
v_res_617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__1(v___x_602_, v_declName_603_, v_as_604_, v_sz_boxed_615_, v_i_boxed_616_, v_b_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec_ref(v_as_604_);
lean_dec_ref(v___x_602_);
return v_res_617_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__2(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_620_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__1));
v___x_621_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__0));
v___x_622_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_621_, v___x_620_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0(lean_object* v_declName_625_, uint8_t v_isMeta_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v___x_634_; lean_object* v_env_638_; lean_object* v___y_640_; lean_object* v___x_653_; 
v___x_634_ = lean_st_ref_get(v___y_632_);
v_env_638_ = lean_ctor_get(v___x_634_, 0);
lean_inc_ref(v_env_638_);
lean_dec(v___x_634_);
v___x_653_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_638_, v_declName_625_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_dec_ref(v_env_638_);
lean_dec(v_declName_625_);
goto v___jp_635_;
}
else
{
lean_object* v_val_654_; lean_object* v___x_655_; lean_object* v_modules_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_val_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_val_654_);
lean_dec_ref(v___x_653_);
v___x_655_ = l_Lean_Environment_header(v_env_638_);
v_modules_656_ = lean_ctor_get(v___x_655_, 3);
lean_inc_ref(v_modules_656_);
lean_dec_ref(v___x_655_);
v___x_657_ = lean_array_get_size(v_modules_656_);
v___x_658_ = lean_nat_dec_lt(v_val_654_, v___x_657_);
if (v___x_658_ == 0)
{
lean_dec_ref(v_modules_656_);
lean_dec(v_val_654_);
lean_dec_ref(v_env_638_);
lean_dec(v_declName_625_);
goto v___jp_635_;
}
else
{
lean_object* v___x_659_; lean_object* v_env_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___y_664_; 
v___x_659_ = lean_st_ref_get(v___y_632_);
v_env_660_ = lean_ctor_get(v___x_659_, 0);
lean_inc_ref(v_env_660_);
lean_dec(v___x_659_);
v___x_661_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__2);
v___x_662_ = lean_array_fget(v_modules_656_, v_val_654_);
lean_dec(v_val_654_);
lean_dec_ref(v_modules_656_);
if (v_isMeta_626_ == 0)
{
lean_dec_ref(v_env_660_);
v___y_664_ = v_isMeta_626_;
goto v___jp_663_;
}
else
{
uint8_t v___x_675_; 
lean_inc(v_declName_625_);
v___x_675_ = l_Lean_isMarkedMeta(v_env_660_, v_declName_625_);
if (v___x_675_ == 0)
{
v___y_664_ = v_isMeta_626_;
goto v___jp_663_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = 0;
v___y_664_ = v___x_676_;
goto v___jp_663_;
}
}
v___jp_663_:
{
lean_object* v_toImport_665_; lean_object* v_module_666_; lean_object* v___x_667_; 
v_toImport_665_ = lean_ctor_get(v___x_662_, 0);
lean_inc_ref(v_toImport_665_);
lean_dec(v___x_662_);
v_module_666_ = lean_ctor_get(v_toImport_665_, 0);
lean_inc(v_module_666_);
lean_dec_ref(v_toImport_665_);
lean_inc(v_declName_625_);
v___x_667_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0(v_module_666_, v___y_664_, v_declName_625_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
if (lean_obj_tag(v___x_667_) == 0)
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
lean_dec_ref(v___x_667_);
v___x_668_ = l_Lean_indirectModUseExt;
v___x_669_ = lean_box(1);
v___x_670_ = lean_box(0);
lean_inc_ref(v_env_638_);
v___x_671_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_661_, v___x_668_, v_env_638_, v___x_669_, v___x_670_);
v___x_672_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg(v___x_671_, v_declName_625_);
lean_dec(v___x_671_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v___x_673_; 
v___x_673_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___closed__3));
v___y_640_ = v___x_673_;
goto v___jp_639_;
}
else
{
lean_object* v_val_674_; 
v_val_674_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_val_674_);
lean_dec_ref(v___x_672_);
v___y_640_ = v_val_674_;
goto v___jp_639_;
}
}
else
{
lean_dec_ref(v_env_638_);
lean_dec(v_declName_625_);
return v___x_667_;
}
}
}
}
v___jp_635_:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_box(0);
v___x_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
return v___x_637_;
}
v___jp_639_:
{
lean_object* v___x_641_; size_t v_sz_642_; size_t v___x_643_; lean_object* v___x_644_; 
v___x_641_ = lean_box(0);
v_sz_642_ = lean_array_size(v___y_640_);
v___x_643_ = ((size_t)0ULL);
v___x_644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__1(v_env_638_, v_declName_625_, v___y_640_, v_sz_642_, v___x_643_, v___x_641_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec_ref(v___y_640_);
lean_dec_ref(v_env_638_);
if (lean_obj_tag(v___x_644_) == 0)
{
lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_651_ == 0)
{
lean_object* v_unused_652_; 
v_unused_652_ = lean_ctor_get(v___x_644_, 0);
lean_dec(v_unused_652_);
v___x_646_ = v___x_644_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_dec(v___x_644_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_641_);
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_641_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
else
{
return v___x_644_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0___boxed(lean_object* v_declName_677_, lean_object* v_isMeta_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
uint8_t v_isMeta_boxed_686_; lean_object* v_res_687_; 
v_isMeta_boxed_686_ = lean_unbox(v_isMeta_678_);
v_res_687_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0(v_declName_677_, v_isMeta_boxed_686_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
return v_res_687_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10(lean_object* v_opts_688_, lean_object* v_opt_689_){
_start:
{
lean_object* v_name_690_; lean_object* v_defValue_691_; lean_object* v_map_692_; lean_object* v___x_693_; 
v_name_690_ = lean_ctor_get(v_opt_689_, 0);
v_defValue_691_ = lean_ctor_get(v_opt_689_, 1);
v_map_692_ = lean_ctor_get(v_opts_688_, 0);
v___x_693_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_692_, v_name_690_);
if (lean_obj_tag(v___x_693_) == 0)
{
uint8_t v___x_694_; 
v___x_694_ = lean_unbox(v_defValue_691_);
return v___x_694_;
}
else
{
lean_object* v_val_695_; 
v_val_695_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_val_695_);
lean_dec_ref(v___x_693_);
if (lean_obj_tag(v_val_695_) == 1)
{
uint8_t v_v_696_; 
v_v_696_ = lean_ctor_get_uint8(v_val_695_, 0);
lean_dec_ref(v_val_695_);
return v_v_696_;
}
else
{
uint8_t v___x_697_; 
lean_dec(v_val_695_);
v___x_697_ = lean_unbox(v_defValue_691_);
return v___x_697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10___boxed(lean_object* v_opts_698_, lean_object* v_opt_699_){
_start:
{
uint8_t v_res_700_; lean_object* v_r_701_; 
v_res_700_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10(v_opts_698_, v_opt_699_);
lean_dec_ref(v_opt_699_);
lean_dec_ref(v_opts_698_);
v_r_701_ = lean_box(v_res_700_);
return v_r_701_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__0(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_box(1);
v___x_703_ = l_Lean_MessageData_ofFormat(v___x_702_);
return v___x_703_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__3(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__2));
v___x_708_ = l_Lean_MessageData_ofFormat(v___x_707_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11(lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
if (lean_obj_tag(v_x_710_) == 0)
{
return v_x_709_;
}
else
{
lean_object* v_head_711_; lean_object* v_tail_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_734_; 
v_head_711_ = lean_ctor_get(v_x_710_, 0);
v_tail_712_ = lean_ctor_get(v_x_710_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_x_710_);
if (v_isSharedCheck_734_ == 0)
{
v___x_714_ = v_x_710_;
v_isShared_715_ = v_isSharedCheck_734_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_tail_712_);
lean_inc(v_head_711_);
lean_dec(v_x_710_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_734_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_before_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_732_; 
v_before_716_ = lean_ctor_get(v_head_711_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_head_711_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v_head_711_, 1);
lean_dec(v_unused_733_);
v___x_718_ = v_head_711_;
v_isShared_719_ = v_isSharedCheck_732_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_before_716_);
lean_dec(v_head_711_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_732_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_720_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__0);
if (v_isShared_719_ == 0)
{
lean_ctor_set_tag(v___x_718_, 7);
lean_ctor_set(v___x_718_, 1, v___x_720_);
lean_ctor_set(v___x_718_, 0, v_x_709_);
v___x_722_ = v___x_718_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_x_709_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_720_);
v___x_722_ = v_reuseFailAlloc_731_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__3);
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 7);
lean_ctor_set(v___x_714_, 1, v___x_723_);
lean_ctor_set(v___x_714_, 0, v___x_722_);
v___x_725_ = v___x_714_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v___x_723_);
v___x_725_ = v_reuseFailAlloc_730_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_726_ = l_Lean_MessageData_ofSyntax(v_before_716_);
v___x_727_ = l_Lean_indentD(v___x_726_);
v___x_728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_725_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v_x_709_ = v___x_728_;
v_x_710_ = v_tail_712_;
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
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__1));
v___x_739_ = l_Lean_MessageData_ofFormat(v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg(lean_object* v_msgData_740_, lean_object* v_macroStack_741_, lean_object* v___y_742_){
_start:
{
lean_object* v_options_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_options_744_ = lean_ctor_get(v___y_742_, 2);
v___x_745_ = l_Lean_Elab_pp_macroStack;
v___x_746_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__10(v_options_744_, v___x_745_);
if (v___x_746_ == 0)
{
lean_object* v___x_747_; 
lean_dec(v_macroStack_741_);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v_msgData_740_);
return v___x_747_;
}
else
{
if (lean_obj_tag(v_macroStack_741_) == 0)
{
lean_object* v___x_748_; 
v___x_748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_748_, 0, v_msgData_740_);
return v___x_748_;
}
else
{
lean_object* v_head_749_; lean_object* v_after_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_765_; 
v_head_749_ = lean_ctor_get(v_macroStack_741_, 0);
lean_inc(v_head_749_);
v_after_750_ = lean_ctor_get(v_head_749_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_head_749_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v_head_749_, 0);
lean_dec(v_unused_766_);
v___x_752_ = v_head_749_;
v_isShared_753_ = v_isSharedCheck_765_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_after_750_);
lean_dec(v_head_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_765_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_754_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11___closed__0);
if (v_isShared_753_ == 0)
{
lean_ctor_set_tag(v___x_752_, 7);
lean_ctor_set(v___x_752_, 1, v___x_754_);
lean_ctor_set(v___x_752_, 0, v_msgData_740_);
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_msgData_740_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v___x_754_);
v___x_756_ = v_reuseFailAlloc_764_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v_msgData_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_757_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___closed__2);
v___x_758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_758_, 0, v___x_756_);
lean_ctor_set(v___x_758_, 1, v___x_757_);
v___x_759_ = l_Lean_MessageData_ofSyntax(v_after_750_);
v___x_760_ = l_Lean_indentD(v___x_759_);
v_msgData_761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_761_, 0, v___x_758_);
lean_ctor_set(v_msgData_761_, 1, v___x_760_);
v___x_762_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5_spec__11(v_msgData_761_, v_macroStack_741_);
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
return v___x_763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg___boxed(lean_object* v_msgData_767_, lean_object* v_macroStack_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg(v_msgData_767_, v_macroStack_768_, v___y_769_);
lean_dec_ref(v___y_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg(lean_object* v_msg_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_){
_start:
{
lean_object* v_ref_780_; lean_object* v___x_781_; lean_object* v_a_782_; lean_object* v_macroStack_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_794_; 
v_ref_780_ = lean_ctor_get(v___y_777_, 5);
v___x_781_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__4(v_msg_772_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
v_a_782_ = lean_ctor_get(v___x_781_, 0);
lean_inc(v_a_782_);
lean_dec_ref(v___x_781_);
v_macroStack_783_ = lean_ctor_get(v___y_773_, 1);
lean_inc(v_macroStack_783_);
lean_dec_ref(v___y_773_);
lean_inc(v_macroStack_783_);
v___x_784_ = l_Lean_Elab_getBetterRef(v_ref_780_, v_macroStack_783_);
v___x_785_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg(v_a_782_, v_macroStack_783_, v___y_777_);
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_794_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_794_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_792_; 
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_784_);
lean_ctor_set(v___x_790_, 1, v_a_786_);
if (v_isShared_789_ == 0)
{
lean_ctor_set_tag(v___x_788_, 1);
lean_ctor_set(v___x_788_, 0, v___x_790_);
v___x_792_ = v___x_788_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg___boxed(lean_object* v_msg_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg(v_msg_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
return v_res_803_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__0));
v___x_806_ = l_Lean_stringToMessageData(v___x_805_);
return v___x_806_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__2));
v___x_809_ = l_Lean_stringToMessageData(v___x_808_);
return v___x_809_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__5(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__4));
v___x_812_ = l_Lean_stringToMessageData(v___x_811_);
return v___x_812_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__7(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__6));
v___x_815_ = l_Lean_stringToMessageData(v___x_814_);
return v___x_815_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__8(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_816_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_));
v___x_817_ = l_Lean_MessageData_ofName(v___x_816_);
return v___x_817_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__9(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_818_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__8, &l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__8);
v___x_819_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__7, &l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__7);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v___x_818_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(lean_object* v_optConfig_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; uint8_t v___y_846_; lean_object* v___y_857_; lean_object* v___y_858_; lean_object* v___y_859_; lean_object* v___y_860_; lean_object* v___y_861_; lean_object* v___y_862_; lean_object* v___y_863_; uint8_t v_recover_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; uint8_t v___x_874_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; lean_object* v___y_881_; 
v_recover_868_ = lean_ctor_get_uint8(v_a_828_, sizeof(void*)*1);
lean_inc(v_optConfig_827_);
v___x_869_ = l_Lean_Parser_Tactic_getConfigItems(v_optConfig_827_);
v___x_870_ = l_Lean_Elab_Tactic_mkConfigItemViews(v___x_869_);
v___x_871_ = lean_array_get_size(v___x_870_);
v___x_872_ = lean_unsigned_to_nat(0u);
v___x_873_ = lean_nat_dec_eq(v___x_871_, v___x_872_);
v___x_874_ = 1;
if (v___x_873_ == 0)
{
lean_object* v___x_925_; lean_object* v_fileName_926_; lean_object* v_fileMap_927_; lean_object* v_options_928_; lean_object* v_currRecDepth_929_; lean_object* v_maxRecDepth_930_; lean_object* v_ref_931_; lean_object* v_currNamespace_932_; lean_object* v_openDecls_933_; lean_object* v_initHeartbeats_934_; lean_object* v_maxHeartbeats_935_; lean_object* v_quotContext_936_; lean_object* v_currMacroScope_937_; uint8_t v_diag_938_; lean_object* v_cancelTk_x3f_939_; uint8_t v_suppressElabErrors_940_; lean_object* v_inheritedTraceOptions_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_962_; 
v___x_925_ = lean_st_ref_get(v_a_834_);
v_fileName_926_ = lean_ctor_get(v_a_833_, 0);
v_fileMap_927_ = lean_ctor_get(v_a_833_, 1);
v_options_928_ = lean_ctor_get(v_a_833_, 2);
v_currRecDepth_929_ = lean_ctor_get(v_a_833_, 3);
v_maxRecDepth_930_ = lean_ctor_get(v_a_833_, 4);
v_ref_931_ = lean_ctor_get(v_a_833_, 5);
v_currNamespace_932_ = lean_ctor_get(v_a_833_, 6);
v_openDecls_933_ = lean_ctor_get(v_a_833_, 7);
v_initHeartbeats_934_ = lean_ctor_get(v_a_833_, 8);
v_maxHeartbeats_935_ = lean_ctor_get(v_a_833_, 9);
v_quotContext_936_ = lean_ctor_get(v_a_833_, 10);
v_currMacroScope_937_ = lean_ctor_get(v_a_833_, 11);
v_diag_938_ = lean_ctor_get_uint8(v_a_833_, sizeof(void*)*14);
v_cancelTk_x3f_939_ = lean_ctor_get(v_a_833_, 12);
v_suppressElabErrors_940_ = lean_ctor_get_uint8(v_a_833_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_941_ = lean_ctor_get(v_a_833_, 13);
v_isSharedCheck_962_ = !lean_is_exclusive(v_a_833_);
if (v_isSharedCheck_962_ == 0)
{
v___x_943_ = v_a_833_;
v_isShared_944_ = v_isSharedCheck_962_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_inheritedTraceOptions_941_);
lean_inc(v_cancelTk_x3f_939_);
lean_inc(v_currMacroScope_937_);
lean_inc(v_quotContext_936_);
lean_inc(v_maxHeartbeats_935_);
lean_inc(v_initHeartbeats_934_);
lean_inc(v_openDecls_933_);
lean_inc(v_currNamespace_932_);
lean_inc(v_ref_931_);
lean_inc(v_maxRecDepth_930_);
lean_inc(v_currRecDepth_929_);
lean_inc(v_options_928_);
lean_inc(v_fileMap_927_);
lean_inc(v_fileName_926_);
lean_dec(v_a_833_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_962_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v_env_945_; lean_object* v_ref_946_; lean_object* v___x_948_; 
v_env_945_ = lean_ctor_get(v___x_925_, 0);
lean_inc_ref(v_env_945_);
lean_dec(v___x_925_);
v_ref_946_ = l_Lean_replaceRef(v_optConfig_827_, v_ref_931_);
lean_dec(v_ref_931_);
lean_dec(v_optConfig_827_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 5, v_ref_946_);
v___x_948_ = v___x_943_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_fileName_926_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_fileMap_927_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v_options_928_);
lean_ctor_set(v_reuseFailAlloc_961_, 3, v_currRecDepth_929_);
lean_ctor_set(v_reuseFailAlloc_961_, 4, v_maxRecDepth_930_);
lean_ctor_set(v_reuseFailAlloc_961_, 5, v_ref_946_);
lean_ctor_set(v_reuseFailAlloc_961_, 6, v_currNamespace_932_);
lean_ctor_set(v_reuseFailAlloc_961_, 7, v_openDecls_933_);
lean_ctor_set(v_reuseFailAlloc_961_, 8, v_initHeartbeats_934_);
lean_ctor_set(v_reuseFailAlloc_961_, 9, v_maxHeartbeats_935_);
lean_ctor_set(v_reuseFailAlloc_961_, 10, v_quotContext_936_);
lean_ctor_set(v_reuseFailAlloc_961_, 11, v_currMacroScope_937_);
lean_ctor_set(v_reuseFailAlloc_961_, 12, v_cancelTk_x3f_939_);
lean_ctor_set(v_reuseFailAlloc_961_, 13, v_inheritedTraceOptions_941_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, sizeof(void*)*14, v_diag_938_);
lean_ctor_set_uint8(v_reuseFailAlloc_961_, sizeof(void*)*14 + 1, v_suppressElabErrors_940_);
v___x_948_ = v_reuseFailAlloc_961_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_949_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_));
v___x_950_ = l_Lean_Environment_contains(v_env_945_, v___x_949_, v___x_874_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec_ref(v___x_870_);
v___x_951_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__9, &l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__9);
v___x_952_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg(v___x_951_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v___x_948_, v_a_834_);
lean_dec(v_a_834_);
lean_dec_ref(v___x_948_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
else
{
v___y_876_ = v_a_829_;
v___y_877_ = v_a_830_;
v___y_878_ = v_a_831_;
v___y_879_ = v_a_832_;
v___y_880_ = v___x_948_;
v___y_881_ = v_a_834_;
goto v___jp_875_;
}
}
}
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec_ref(v___x_870_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_optConfig_827_);
v___x_963_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__10));
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
return v___x_964_;
}
v___jp_836_:
{
if (v___y_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec_ref(v___y_838_);
v___x_847_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__1, &l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__1);
v___x_848_ = l_Lean_MessageData_ofExpr(v___y_841_);
v___x_849_ = l_Lean_indentD(v___x_848_);
v___x_850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_847_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__3, &l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__3);
v___x_852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_850_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = l_Lean_Exception_toMessageData(v___y_837_);
v___x_854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_852_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg(v___x_854_, v___y_842_, v___y_844_, v___y_845_, v___y_840_, v___y_839_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
return v___x_855_;
}
else
{
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec_ref(v___y_837_);
return v___y_838_;
}
}
v___jp_856_:
{
lean_object* v___x_864_; 
lean_inc(v___y_863_);
lean_inc_ref(v___y_862_);
lean_inc(v___y_861_);
lean_inc_ref(v___y_860_);
lean_inc_ref(v___y_857_);
v___x_864_ = l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_(v___y_857_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_dec(v___y_863_);
lean_dec_ref(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
lean_dec_ref(v___y_857_);
return v___x_864_;
}
else
{
lean_object* v_a_865_; uint8_t v___x_866_; 
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
v___x_866_ = l_Lean_Exception_isInterrupt(v_a_865_);
if (v___x_866_ == 0)
{
uint8_t v___x_867_; 
lean_inc(v_a_865_);
v___x_867_ = l_Lean_Exception_isRuntime(v_a_865_);
v___y_837_ = v_a_865_;
v___y_838_ = v___x_864_;
v___y_839_ = v___y_862_;
v___y_840_ = v___y_861_;
v___y_841_ = v___y_857_;
v___y_842_ = v___y_858_;
v___y_843_ = v___y_863_;
v___y_844_ = v___y_859_;
v___y_845_ = v___y_860_;
v___y_846_ = v___x_867_;
goto v___jp_836_;
}
else
{
v___y_837_ = v_a_865_;
v___y_838_ = v___x_864_;
v___y_839_ = v___y_862_;
v___y_840_ = v___y_861_;
v___y_841_ = v___y_857_;
v___y_842_ = v___y_858_;
v___y_843_ = v___y_863_;
v___y_844_ = v___y_859_;
v___y_845_ = v___y_860_;
v___y_846_ = v___x_866_;
goto v___jp_836_;
}
}
}
v___jp_875_:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_644698046____hygCtx___hyg_3_));
v___x_883_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0(v___x_882_, v___x_874_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v___x_884_; 
lean_dec_ref(v___x_883_);
lean_inc(v___y_881_);
lean_inc_ref(v___y_880_);
lean_inc(v___y_879_);
lean_inc_ref(v___y_878_);
lean_inc(v___y_877_);
lean_inc_ref(v___y_876_);
v___x_884_ = l_Lean_Elab_Tactic_elabConfig(v_recover_868_, v___x_882_, v___x_870_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_908_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_908_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_908_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_908_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_908_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
uint8_t v___x_889_; 
v___x_889_ = l_Lean_Expr_hasSyntheticSorry(v_a_885_);
if (v___x_889_ == 0)
{
uint8_t v___x_890_; 
lean_del_object(v___x_887_);
v___x_890_ = l_Lean_Expr_hasSorry(v_a_885_);
if (v___x_890_ == 0)
{
v___y_857_ = v_a_885_;
v___y_858_ = v___y_876_;
v___y_859_ = v___y_877_;
v___y_860_ = v___y_878_;
v___y_861_ = v___y_879_;
v___y_862_ = v___y_880_;
v___y_863_ = v___y_881_;
goto v___jp_856_;
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_900_; 
lean_dec(v_a_885_);
v___x_891_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__5, &l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___closed__5);
v___x_892_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg(v___x_891_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
v_a_893_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_900_ == 0)
{
v___x_895_ = v___x_892_;
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_893_);
lean_dec(v___x_892_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_900_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_898_; 
if (v_isShared_896_ == 0)
{
v___x_898_ = v___x_895_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
else
{
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_906_; 
lean_dec(v_a_885_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
v___x_901_ = lean_unsigned_to_nat(10u);
v___x_902_ = lean_unsigned_to_nat(100000u);
v___x_903_ = 0;
v___x_904_ = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(v___x_904_, 0, v___x_901_);
lean_ctor_set(v___x_904_, 1, v___x_902_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*2, v___x_874_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*2 + 1, v___x_874_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*2 + 2, v___x_873_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*2 + 3, v___x_874_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*2 + 4, v___x_874_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*2 + 5, v___x_874_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*2 + 6, v___x_874_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*2 + 7, v___x_874_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*2 + 8, v___x_873_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*2 + 9, v___x_873_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*2 + 10, v___x_903_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_904_);
v___x_906_ = v___x_887_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
v___x_906_ = v_reuseFailAlloc_907_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
return v___x_906_;
}
}
}
}
else
{
lean_object* v_a_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_916_; 
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
v_a_909_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_916_ == 0)
{
v___x_911_ = v___x_884_;
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_a_909_);
lean_dec(v___x_884_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_916_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_914_; 
if (v_isShared_912_ == 0)
{
v___x_914_ = v___x_911_;
goto v_reusejp_913_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
v___x_914_ = v_reuseFailAlloc_915_;
goto v_reusejp_913_;
}
v_reusejp_913_:
{
return v___x_914_;
}
}
}
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec_ref(v___x_870_);
v_a_917_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_883_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_883_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg___boxed(lean_object* v_optConfig_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(v_optConfig_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
lean_dec_ref(v_a_966_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig(lean_object* v_optConfig_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___redArg(v_optConfig_975_, v_a_976_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig___boxed(lean_object* v_optConfig_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig(v_optConfig_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_);
lean_dec(v_a_988_);
lean_dec_ref(v_a_987_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1(lean_object* v_00_u03b1_997_, lean_object* v_msg_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___redArg(v_msg_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
return v___x_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1___boxed(lean_object* v_00_u03b1_1007_, lean_object* v_msg_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1(v_00_u03b1_1007_, v_msg_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2(lean_object* v_cls_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___redArg(v_cls_1017_, v___y_1022_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__2(v_cls_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2(lean_object* v_00_u03b2_1035_, lean_object* v_m_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___redArg(v_m_1036_, v_a_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1039_, lean_object* v_m_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2(v_00_u03b2_1039_, v_m_1040_, v_a_1041_);
lean_dec(v_a_1041_);
lean_dec_ref(v_m_1040_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5(lean_object* v_msgData_1043_, lean_object* v_macroStack_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___redArg(v_msgData_1043_, v_macroStack_1044_, v___y_1049_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5___boxed(lean_object* v_msgData_1053_, lean_object* v_macroStack_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__1_spec__5(v_msgData_1053_, v_macroStack_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
return v_res_1062_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1063_, lean_object* v_x_1064_, lean_object* v_x_1065_){
_start:
{
uint8_t v___x_1066_; 
v___x_1066_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___redArg(v_x_1064_, v_x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1067_, lean_object* v_x_1068_, lean_object* v_x_1069_){
_start:
{
uint8_t v_res_1070_; lean_object* v_r_1071_; 
v_res_1070_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1(v_00_u03b2_1067_, v_x_1068_, v_x_1069_);
lean_dec_ref(v_x_1069_);
v_r_1071_ = lean_box(v_res_1070_);
return v_r_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3(lean_object* v_cls_1072_, lean_object* v_msg_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___redArg(v_cls_1072_, v_msg_1073_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3___boxed(lean_object* v_cls_1082_, lean_object* v_msg_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__3(v_cls_1082_, v_msg_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_1092_, lean_object* v_a_1093_, lean_object* v_x_1094_){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__6___redArg(v_a_1093_, v_x_1094_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_1096_, lean_object* v_a_1097_, lean_object* v_x_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__2_spec__6(v_00_u03b2_1096_, v_a_1097_, v_x_1098_);
lean_dec(v_x_1098_);
lean_dec(v_a_1097_);
return v_res_1099_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_1100_, lean_object* v_x_1101_, size_t v_x_1102_, lean_object* v_x_1103_){
_start:
{
uint8_t v___x_1104_; 
v___x_1104_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1101_, v_x_1102_, v_x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_){
_start:
{
size_t v_x_13691__boxed_1109_; uint8_t v_res_1110_; lean_object* v_r_1111_; 
v_x_13691__boxed_1109_ = lean_unbox_usize(v_x_1107_);
lean_dec(v_x_1107_);
v_res_1110_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_1105_, v_x_1106_, v_x_13691__boxed_1109_, v_x_1108_);
lean_dec_ref(v_x_1108_);
v_r_1111_ = lean_box(v_res_1110_);
return v_r_1111_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_1112_, lean_object* v_keys_1113_, lean_object* v_vals_1114_, lean_object* v_heq_1115_, lean_object* v_i_1116_, lean_object* v_k_1117_){
_start:
{
uint8_t v___x_1118_; 
v___x_1118_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__10___redArg(v_keys_1113_, v_i_1116_, v_k_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_00_u03b2_1119_, lean_object* v_keys_1120_, lean_object* v_vals_1121_, lean_object* v_heq_1122_, lean_object* v_i_1123_, lean_object* v_k_1124_){
_start:
{
uint8_t v_res_1125_; lean_object* v_r_1126_; 
v_res_1125_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_BVDecide_Frontend_elabBVDecideConfig_spec__0_spec__0_spec__1_spec__4_spec__10(v_00_u03b2_1119_, v_keys_1120_, v_vals_1121_, v_heq_1122_, v_i_1123_, v_k_1124_);
lean_dec_ref(v_k_1124_);
lean_dec_ref(v_vals_1121_);
lean_dec_ref(v_keys_1120_);
v_r_1126_ = lean_box(v_res_1125_);
return v_r_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1140_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_));
v___x_1141_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_));
v___x_1142_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_));
v___x_1143_ = l_Lean_Meta_registerSimpAttr(v___x_1140_, v___x_1141_, v___x_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2____boxed(lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3513353098____hygCtx___hyg_2_();
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1159_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_));
v___x_1160_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_));
v___x_1161_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__4_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_));
v___x_1162_ = l_Lean_Meta_registerSimpAttr(v___x_1159_, v___x_1160_, v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2____boxed(lean_object* v_a_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_3750720685____hygCtx___hyg_2_();
return v_res_1164_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0(void){
_start:
{
lean_object* v___x_1165_; 
v___x_1165_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1165_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__0);
v___x_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1167_, 0, v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0___closed__1);
return v___x_1169_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_1170_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_Lean_PersistentHashMap_empty___at___00Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__spec__0(lean_box(0));
return v___x_1171_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_, &l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_);
v___x_1173_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_, &l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_);
v___x_1174_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v___x_1173_);
lean_ctor_set(v___x_1174_, 2, v___x_1172_);
lean_ctor_set(v___x_1174_, 3, v___x_1172_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1176_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_, &l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2__once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_);
v___x_1177_ = lean_st_mk_ref(v___x_1176_);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2____boxed(lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2011030299____hygCtx___hyg_2_();
return v_res_1180_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; 
v___x_1185_ = l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef;
v___x_1186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1186_, 0, v___x_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1196_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_));
v___x_1197_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__2_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_));
v___x_1198_ = lean_obj_once(&l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_, &l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2__once, _init_l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__3_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_);
v___x_1199_ = ((lean_object*)(l_Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__5_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_));
v___x_1200_ = l_Lean_Meta_Simp_registerSimprocAttr(v___x_1196_, v___x_1197_, v___x_1198_, v___x_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2____boxed(lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_2218032216____hygCtx___hyg_2_();
return v_res_1202_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__0);
v___x_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
return v___x_1205_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v___x_1207_);
lean_ctor_set(v___x_1208_, 2, v___x_1207_);
lean_ctor_set(v___x_1208_, 3, v___x_1206_);
lean_ctor_set(v___x_1208_, 4, v___x_1206_);
lean_ctor_set(v___x_1208_, 5, v___x_1206_);
lean_ctor_set(v___x_1208_, 6, v___x_1206_);
lean_ctor_set(v___x_1208_, 7, v___x_1206_);
lean_ctor_set(v___x_1208_, 8, v___x_1206_);
return v___x_1208_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = lean_unsigned_to_nat(32u);
v___x_1210_ = lean_mk_empty_array_with_capacity(v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1210_);
return v___x_1211_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1212_ = ((size_t)5ULL);
v___x_1213_ = lean_unsigned_to_nat(0u);
v___x_1214_ = lean_unsigned_to_nat(32u);
v___x_1215_ = lean_mk_empty_array_with_capacity(v___x_1214_);
v___x_1216_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__3);
v___x_1217_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v___x_1215_);
lean_ctor_set(v___x_1217_, 2, v___x_1213_);
lean_ctor_set(v___x_1217_, 3, v___x_1213_);
lean_ctor_set_usize(v___x_1217_, 4, v___x_1212_);
return v___x_1217_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1218_ = lean_box(1);
v___x_1219_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__4);
v___x_1220_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__1);
v___x_1221_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v___x_1219_);
lean_ctor_set(v___x_1221_, 2, v___x_1218_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0(lean_object* v_msgData_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v___x_1226_; lean_object* v_env_1227_; lean_object* v_options_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1226_ = lean_st_ref_get(v___y_1224_);
v_env_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc_ref(v_env_1227_);
lean_dec(v___x_1226_);
v_options_1228_ = lean_ctor_get(v___y_1223_, 2);
v___x_1229_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2);
v___x_1230_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_1228_);
v___x_1231_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1231_, 0, v_env_1227_);
lean_ctor_set(v___x_1231_, 1, v___x_1229_);
lean_ctor_set(v___x_1231_, 2, v___x_1230_);
lean_ctor_set(v___x_1231_, 3, v_options_1228_);
v___x_1232_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set(v___x_1232_, 1, v_msgData_1222_);
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___boxed(lean_object* v_msgData_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0(v_msgData_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(lean_object* v_msg_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_){
_start:
{
lean_object* v_ref_1243_; lean_object* v___x_1244_; lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1253_; 
v_ref_1243_ = lean_ctor_get(v___y_1240_, 5);
v___x_1244_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0(v_msg_1239_, v___y_1240_, v___y_1241_);
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1247_ = v___x_1244_;
v_isShared_1248_ = v_isSharedCheck_1253_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1244_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1253_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1249_; lean_object* v___x_1251_; 
lean_inc(v_ref_1243_);
v___x_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1249_, 0, v_ref_1243_);
lean_ctor_set(v___x_1249_, 1, v_a_1245_);
if (v_isShared_1248_ == 0)
{
lean_ctor_set_tag(v___x_1247_, 1);
lean_ctor_set(v___x_1247_, 0, v___x_1249_);
v___x_1251_ = v___x_1247_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg___boxed(lean_object* v_msg_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(v_msg_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(lean_object* v_ref_1259_, lean_object* v_msg_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_fileName_1264_; lean_object* v_fileMap_1265_; lean_object* v_options_1266_; lean_object* v_currRecDepth_1267_; lean_object* v_maxRecDepth_1268_; lean_object* v_ref_1269_; lean_object* v_currNamespace_1270_; lean_object* v_openDecls_1271_; lean_object* v_initHeartbeats_1272_; lean_object* v_maxHeartbeats_1273_; lean_object* v_quotContext_1274_; lean_object* v_currMacroScope_1275_; uint8_t v_diag_1276_; lean_object* v_cancelTk_x3f_1277_; uint8_t v_suppressElabErrors_1278_; lean_object* v_inheritedTraceOptions_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1288_; 
v_fileName_1264_ = lean_ctor_get(v___y_1261_, 0);
v_fileMap_1265_ = lean_ctor_get(v___y_1261_, 1);
v_options_1266_ = lean_ctor_get(v___y_1261_, 2);
v_currRecDepth_1267_ = lean_ctor_get(v___y_1261_, 3);
v_maxRecDepth_1268_ = lean_ctor_get(v___y_1261_, 4);
v_ref_1269_ = lean_ctor_get(v___y_1261_, 5);
v_currNamespace_1270_ = lean_ctor_get(v___y_1261_, 6);
v_openDecls_1271_ = lean_ctor_get(v___y_1261_, 7);
v_initHeartbeats_1272_ = lean_ctor_get(v___y_1261_, 8);
v_maxHeartbeats_1273_ = lean_ctor_get(v___y_1261_, 9);
v_quotContext_1274_ = lean_ctor_get(v___y_1261_, 10);
v_currMacroScope_1275_ = lean_ctor_get(v___y_1261_, 11);
v_diag_1276_ = lean_ctor_get_uint8(v___y_1261_, sizeof(void*)*14);
v_cancelTk_x3f_1277_ = lean_ctor_get(v___y_1261_, 12);
v_suppressElabErrors_1278_ = lean_ctor_get_uint8(v___y_1261_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1279_ = lean_ctor_get(v___y_1261_, 13);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___y_1261_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1281_ = v___y_1261_;
v_isShared_1282_ = v_isSharedCheck_1288_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_inheritedTraceOptions_1279_);
lean_inc(v_cancelTk_x3f_1277_);
lean_inc(v_currMacroScope_1275_);
lean_inc(v_quotContext_1274_);
lean_inc(v_maxHeartbeats_1273_);
lean_inc(v_initHeartbeats_1272_);
lean_inc(v_openDecls_1271_);
lean_inc(v_currNamespace_1270_);
lean_inc(v_ref_1269_);
lean_inc(v_maxRecDepth_1268_);
lean_inc(v_currRecDepth_1267_);
lean_inc(v_options_1266_);
lean_inc(v_fileMap_1265_);
lean_inc(v_fileName_1264_);
lean_dec(v___y_1261_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1288_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_ref_1283_; lean_object* v___x_1285_; 
v_ref_1283_ = l_Lean_replaceRef(v_ref_1259_, v_ref_1269_);
lean_dec(v_ref_1269_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 5, v_ref_1283_);
v___x_1285_ = v___x_1281_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_fileName_1264_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_fileMap_1265_);
lean_ctor_set(v_reuseFailAlloc_1287_, 2, v_options_1266_);
lean_ctor_set(v_reuseFailAlloc_1287_, 3, v_currRecDepth_1267_);
lean_ctor_set(v_reuseFailAlloc_1287_, 4, v_maxRecDepth_1268_);
lean_ctor_set(v_reuseFailAlloc_1287_, 5, v_ref_1283_);
lean_ctor_set(v_reuseFailAlloc_1287_, 6, v_currNamespace_1270_);
lean_ctor_set(v_reuseFailAlloc_1287_, 7, v_openDecls_1271_);
lean_ctor_set(v_reuseFailAlloc_1287_, 8, v_initHeartbeats_1272_);
lean_ctor_set(v_reuseFailAlloc_1287_, 9, v_maxHeartbeats_1273_);
lean_ctor_set(v_reuseFailAlloc_1287_, 10, v_quotContext_1274_);
lean_ctor_set(v_reuseFailAlloc_1287_, 11, v_currMacroScope_1275_);
lean_ctor_set(v_reuseFailAlloc_1287_, 12, v_cancelTk_x3f_1277_);
lean_ctor_set(v_reuseFailAlloc_1287_, 13, v_inheritedTraceOptions_1279_);
lean_ctor_set_uint8(v_reuseFailAlloc_1287_, sizeof(void*)*14, v_diag_1276_);
lean_ctor_set_uint8(v_reuseFailAlloc_1287_, sizeof(void*)*14 + 1, v_suppressElabErrors_1278_);
v___x_1285_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(v_msg_1260_, v___x_1285_, v___y_1262_);
lean_dec_ref(v___x_1285_);
return v___x_1286_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_ref_1289_, lean_object* v_msg_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1289_, v_msg_1290_, v___y_1291_, v___y_1292_);
lean_dec(v___y_1292_);
lean_dec(v_ref_1289_);
return v_res_1294_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__0));
v___x_1297_ = l_Lean_stringToMessageData(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__2));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__4));
v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
return v___x_1303_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__6));
v___x_1306_ = l_Lean_stringToMessageData(v___x_1305_);
return v___x_1306_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__8));
v___x_1309_ = l_Lean_stringToMessageData(v___x_1308_);
return v___x_1309_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__10));
v___x_1312_ = l_Lean_stringToMessageData(v___x_1311_);
return v___x_1312_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__12));
v___x_1315_ = l_Lean_stringToMessageData(v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(lean_object* v_msg_1316_, lean_object* v_declHint_1317_, lean_object* v___y_1318_){
_start:
{
lean_object* v___x_1320_; lean_object* v_env_1321_; uint8_t v___x_1322_; 
v___x_1320_ = lean_st_ref_get(v___y_1318_);
v_env_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc_ref(v_env_1321_);
lean_dec(v___x_1320_);
v___x_1322_ = l_Lean_Name_isAnonymous(v_declHint_1317_);
if (v___x_1322_ == 0)
{
uint8_t v_isExporting_1323_; 
v_isExporting_1323_ = lean_ctor_get_uint8(v_env_1321_, sizeof(void*)*8);
if (v_isExporting_1323_ == 0)
{
lean_object* v___x_1324_; 
lean_dec_ref(v_env_1321_);
lean_dec(v_declHint_1317_);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v_msg_1316_);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
lean_inc_ref(v_env_1321_);
v___x_1325_ = l_Lean_Environment_setExporting(v_env_1321_, v___x_1322_);
lean_inc(v_declHint_1317_);
lean_inc_ref(v___x_1325_);
v___x_1326_ = l_Lean_Environment_contains(v___x_1325_, v_declHint_1317_, v_isExporting_1323_);
if (v___x_1326_ == 0)
{
lean_object* v___x_1327_; 
lean_dec_ref(v___x_1325_);
lean_dec_ref(v_env_1321_);
lean_dec(v_declHint_1317_);
v___x_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1327_, 0, v_msg_1316_);
return v___x_1327_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_c_1333_; lean_object* v___x_1334_; 
v___x_1328_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__2);
v___x_1329_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0_spec__0___closed__5);
v___x_1330_ = l_Lean_Options_empty;
v___x_1331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1325_);
lean_ctor_set(v___x_1331_, 1, v___x_1328_);
lean_ctor_set(v___x_1331_, 2, v___x_1329_);
lean_ctor_set(v___x_1331_, 3, v___x_1330_);
lean_inc(v_declHint_1317_);
v___x_1332_ = l_Lean_MessageData_ofConstName(v_declHint_1317_, v___x_1322_);
v_c_1333_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1333_, 0, v___x_1331_);
lean_ctor_set(v_c_1333_, 1, v___x_1332_);
v___x_1334_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1321_, v_declHint_1317_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
lean_dec_ref(v_env_1321_);
lean_dec(v_declHint_1317_);
v___x_1335_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
lean_ctor_set(v___x_1336_, 1, v_c_1333_);
v___x_1337_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__3);
v___x_1338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1336_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
v___x_1339_ = l_Lean_MessageData_note(v___x_1338_);
v___x_1340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1340_, 0, v_msg_1316_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
return v___x_1341_;
}
else
{
lean_object* v_val_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1377_; 
v_val_1342_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1344_ = v___x_1334_;
v_isShared_1345_ = v_isSharedCheck_1377_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_val_1342_);
lean_dec(v___x_1334_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1377_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v_mod_1349_; uint8_t v___x_1350_; 
v___x_1346_ = lean_box(0);
v___x_1347_ = l_Lean_Environment_header(v_env_1321_);
lean_dec_ref(v_env_1321_);
v___x_1348_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1347_);
v_mod_1349_ = lean_array_get(v___x_1346_, v___x_1348_, v_val_1342_);
lean_dec(v_val_1342_);
lean_dec_ref(v___x_1348_);
v___x_1350_ = l_Lean_isPrivateName(v_declHint_1317_);
lean_dec(v_declHint_1317_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1351_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__5);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
lean_ctor_set(v___x_1352_, 1, v_c_1333_);
v___x_1353_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__7);
v___x_1354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1352_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = l_Lean_MessageData_ofName(v_mod_1349_);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__9);
v___x_1358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1356_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = l_Lean_MessageData_note(v___x_1358_);
v___x_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1360_, 0, v_msg_1316_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1360_);
v___x_1362_ = v___x_1344_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1364_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__1);
v___x_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
lean_ctor_set(v___x_1365_, 1, v_c_1333_);
v___x_1366_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__11);
v___x_1367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1365_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = l_Lean_MessageData_ofName(v_mod_1349_);
v___x_1369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1367_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___closed__13);
v___x_1371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1369_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = l_Lean_MessageData_note(v___x_1371_);
v___x_1373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_msg_1316_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1373_);
v___x_1375_ = v___x_1344_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1378_; 
lean_dec_ref(v_env_1321_);
lean_dec(v_declHint_1317_);
v___x_1378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1378_, 0, v_msg_1316_);
return v___x_1378_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg___boxed(lean_object* v_msg_1379_, lean_object* v_declHint_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1379_, v_declHint_1380_, v___y_1381_);
lean_dec(v___y_1381_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1384_, lean_object* v_declHint_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_){
_start:
{
lean_object* v___x_1389_; lean_object* v_a_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1399_; 
v___x_1389_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1384_, v_declHint_1385_, v___y_1387_);
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1399_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1399_ == 0)
{
v___x_1392_ = v___x_1389_;
v_isShared_1393_ = v_isSharedCheck_1399_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_a_1390_);
lean_dec(v___x_1389_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1399_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1394_ = l_Lean_unknownIdentifierMessageTag;
v___x_1395_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v_a_1390_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 0, v___x_1395_);
v___x_1397_ = v___x_1392_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1400_, lean_object* v_declHint_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1400_, v_declHint_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_ref_1406_, lean_object* v_msg_1407_, lean_object* v_declHint_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; lean_object* v_a_1413_; lean_object* v___x_1414_; 
v___x_1412_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5(v_msg_1407_, v_declHint_1408_, v___y_1409_, v___y_1410_);
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref(v___x_1412_);
v___x_1414_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1406_, v_a_1413_, v___y_1409_, v___y_1410_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_ref_1415_, lean_object* v_msg_1416_, lean_object* v_declHint_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1415_, v_msg_1416_, v_declHint_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec(v_ref_1415_);
return v_res_1421_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__0));
v___x_1424_ = l_Lean_stringToMessageData(v___x_1423_);
return v___x_1424_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__2));
v___x_1427_ = l_Lean_stringToMessageData(v___x_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg(lean_object* v_ref_1428_, lean_object* v_constName_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v___x_1433_; uint8_t v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1433_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__1);
v___x_1434_ = 0;
lean_inc(v_constName_1429_);
v___x_1435_ = l_Lean_MessageData_ofConstName(v_constName_1429_, v___x_1434_);
v___x_1436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1433_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___closed__3);
v___x_1438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1436_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1428_, v___x_1438_, v_constName_1429_, v___y_1430_, v___y_1431_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1440_, lean_object* v_constName_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg(v_ref_1440_, v_constName_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec(v_ref_1440_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg(lean_object* v_constName_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_ref_1450_; lean_object* v___x_1451_; 
v_ref_1450_ = lean_ctor_get(v___y_1447_, 5);
lean_inc(v_ref_1450_);
v___x_1451_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg(v_ref_1450_, v_constName_1446_, v___y_1447_, v___y_1448_);
lean_dec(v_ref_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg___boxed(lean_object* v_constName_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg(v_constName_1452_, v___y_1453_, v___y_1454_);
lean_dec(v___y_1454_);
return v_res_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1(lean_object* v_constName_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___x_1461_; lean_object* v_env_1462_; uint8_t v___x_1463_; lean_object* v___x_1464_; 
v___x_1461_ = lean_st_ref_get(v___y_1459_);
v_env_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc_ref(v_env_1462_);
lean_dec(v___x_1461_);
v___x_1463_ = 0;
lean_inc(v_constName_1457_);
v___x_1464_ = l_Lean_Environment_find_x3f(v_env_1462_, v_constName_1457_, v___x_1463_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg(v_constName_1457_, v___y_1458_, v___y_1459_);
return v___x_1465_;
}
else
{
lean_object* v_val_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec_ref(v___y_1458_);
lean_dec(v_constName_1457_);
v_val_1466_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1464_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_val_1466_);
lean_dec(v___x_1464_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
lean_ctor_set_tag(v___x_1468_, 0);
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_val_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1___boxed(lean_object* v_constName_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1(v_constName_1474_, v___y_1475_, v___y_1476_);
lean_dec(v___y_1476_);
return v_res_1478_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1487_ = lean_box(0);
v___x_1488_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__4));
v___x_1489_ = l_Lean_mkConst(v___x_1488_, v___x_1487_);
return v___x_1489_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1494_ = lean_box(0);
v___x_1495_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__7));
v___x_1496_ = l_Lean_mkConst(v___x_1495_, v___x_1494_);
return v___x_1496_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__9));
v___x_1499_ = l_Lean_stringToMessageData(v___x_1498_);
return v___x_1499_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_unsigned_to_nat(0u);
v___x_1508_ = l_Lean_Level_ofNat(v___x_1507_);
return v___x_1508_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1509_ = lean_box(0);
v___x_1510_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16);
v___x_1511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
lean_ctor_set(v___x_1511_, 1, v___x_1509_);
return v___x_1511_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__17);
v___x_1513_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__16);
v___x_1514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v___x_1512_);
return v___x_1514_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__18);
v___x_1516_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__15));
v___x_1517_ = l_Lean_mkConst(v___x_1516_, v___x_1515_);
return v___x_1517_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1523_ = lean_box(0);
v___x_1524_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__20));
v___x_1525_ = l_Lean_mkConst(v___x_1524_, v___x_1523_);
return v___x_1525_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1532_ = lean_box(0);
v___x_1533_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__23));
v___x_1534_ = l_Lean_mkConst(v___x_1533_, v___x_1532_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin(lean_object* v_declName_1542_, lean_object* v_stx_1543_, lean_object* v_addDeclName_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v___y_1549_; lean_object* v___y_1550_; lean_object* v___y_1551_; lean_object* v___y_1552_; lean_object* v___y_1553_; lean_object* v___y_1554_; uint8_t v___y_1575_; lean_object* v_procExpr_1576_; lean_object* v___y_1577_; lean_object* v___y_1578_; uint8_t v___y_1585_; lean_object* v___y_1586_; lean_object* v___y_1587_; uint8_t v___y_1599_; lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; 
v___x_1634_ = lean_unsigned_to_nat(1u);
v___x_1635_ = l_Lean_Syntax_getArg(v_stx_1543_, v___x_1634_);
v___x_1636_ = l_Lean_Syntax_isNone(v___x_1635_);
if (v___x_1636_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v___x_1637_ = lean_unsigned_to_nat(0u);
v___x_1638_ = l_Lean_Syntax_getArg(v___x_1635_, v___x_1637_);
lean_dec(v___x_1635_);
v___x_1639_ = l_Lean_Syntax_getKind(v___x_1638_);
v___x_1640_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__27));
v___x_1641_ = lean_name_eq(v___x_1639_, v___x_1640_);
lean_dec(v___x_1639_);
v___y_1599_ = v___x_1641_;
goto v___jp_1598_;
}
else
{
lean_dec(v___x_1635_);
v___y_1599_ = v___x_1636_;
goto v___jp_1598_;
}
v___jp_1548_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__1));
v___x_1556_ = l_Lean_Name_append(v_declName_1542_, v___x_1555_);
lean_inc(v___y_1551_);
lean_inc_ref(v___y_1552_);
v___x_1557_ = l_Lean_Core_mkFreshUserName(v___x_1556_, v___y_1552_, v___y_1551_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = lean_unsigned_to_nat(3u);
v___x_1560_ = lean_mk_empty_array_with_capacity(v___x_1559_);
v___x_1561_ = lean_array_push(v___x_1560_, v___y_1549_);
v___x_1562_ = lean_array_push(v___x_1561_, v___y_1554_);
v___x_1563_ = lean_array_push(v___x_1562_, v___y_1553_);
v___x_1564_ = l_Lean_mkAppN(v___y_1550_, v___x_1563_);
lean_dec_ref(v___x_1563_);
v___x_1565_ = l_Lean_declareBuiltin(v_a_1558_, v___x_1564_, v___y_1552_, v___y_1551_);
return v___x_1565_;
}
else
{
lean_object* v_a_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1573_; 
lean_dec_ref(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec_ref(v___y_1549_);
v_a_1566_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1568_ = v___x_1557_;
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_a_1566_);
lean_dec(v___x_1557_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1573_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1571_; 
if (v_isShared_1569_ == 0)
{
v___x_1571_ = v___x_1568_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v_a_1566_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
v___jp_1574_:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1579_ = lean_box(0);
v___x_1580_ = l_Lean_mkConst(v_addDeclName_1544_, v___x_1579_);
lean_inc(v_declName_1542_);
v___x_1581_ = l_Lean_instToExprName___private__1(v_declName_1542_);
if (v___y_1575_ == 0)
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__5);
v___y_1549_ = v___x_1581_;
v___y_1550_ = v___x_1580_;
v___y_1551_ = v___y_1578_;
v___y_1552_ = v___y_1577_;
v___y_1553_ = v_procExpr_1576_;
v___y_1554_ = v___x_1582_;
goto v___jp_1548_;
}
else
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__8);
v___y_1549_ = v___x_1581_;
v___y_1550_ = v___x_1580_;
v___y_1551_ = v___y_1578_;
v___y_1552_ = v___y_1577_;
v___y_1553_ = v_procExpr_1576_;
v___y_1554_ = v___x_1583_;
goto v___jp_1548_;
}
}
v___jp_1584_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v_a_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1597_; 
v___x_1588_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__10);
v___x_1589_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(v___x_1588_, v___y_1586_, v___y_1587_);
lean_dec(v___y_1587_);
lean_dec_ref(v___y_1586_);
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1592_ = v___x_1589_;
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1597_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1595_; 
if (v_isShared_1593_ == 0)
{
v___x_1595_ = v___x_1592_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_a_1590_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
v___jp_1598_:
{
lean_object* v___x_1600_; 
lean_inc_ref(v_a_1545_);
lean_inc(v_declName_1542_);
v___x_1600_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1(v_declName_1542_, v_a_1545_, v_a_1546_);
if (lean_obj_tag(v___x_1600_) == 0)
{
lean_object* v_a_1601_; lean_object* v___x_1602_; 
v_a_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_a_1601_);
lean_dec_ref(v___x_1600_);
v___x_1602_ = l_Lean_ConstantInfo_type(v_a_1601_);
lean_dec(v_a_1601_);
if (lean_obj_tag(v___x_1602_) == 4)
{
lean_object* v_declName_1603_; 
v_declName_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_declName_1603_);
lean_dec_ref(v___x_1602_);
if (lean_obj_tag(v_declName_1603_) == 1)
{
lean_object* v_pre_1604_; 
v_pre_1604_ = lean_ctor_get(v_declName_1603_, 0);
lean_inc(v_pre_1604_);
if (lean_obj_tag(v_pre_1604_) == 1)
{
lean_object* v_pre_1605_; 
v_pre_1605_ = lean_ctor_get(v_pre_1604_, 0);
lean_inc(v_pre_1605_);
if (lean_obj_tag(v_pre_1605_) == 1)
{
lean_object* v_pre_1606_; 
v_pre_1606_ = lean_ctor_get(v_pre_1605_, 0);
lean_inc(v_pre_1606_);
if (lean_obj_tag(v_pre_1606_) == 1)
{
lean_object* v_pre_1607_; 
v_pre_1607_ = lean_ctor_get(v_pre_1606_, 0);
if (lean_obj_tag(v_pre_1607_) == 0)
{
lean_object* v_str_1608_; lean_object* v_str_1609_; lean_object* v_str_1610_; lean_object* v_str_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v_str_1608_ = lean_ctor_get(v_declName_1603_, 1);
lean_inc_ref(v_str_1608_);
lean_dec_ref(v_declName_1603_);
v_str_1609_ = lean_ctor_get(v_pre_1604_, 1);
lean_inc_ref(v_str_1609_);
lean_dec_ref(v_pre_1604_);
v_str_1610_ = lean_ctor_get(v_pre_1605_, 1);
lean_inc_ref(v_str_1610_);
lean_dec_ref(v_pre_1605_);
v_str_1611_ = lean_ctor_get(v_pre_1606_, 1);
lean_inc_ref(v_str_1611_);
lean_dec_ref(v_pre_1606_);
v___x_1612_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__6_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_1613_ = lean_string_dec_eq(v_str_1611_, v___x_1612_);
lean_dec_ref(v_str_1611_);
if (v___x_1613_ == 0)
{
lean_dec_ref(v_str_1610_);
lean_dec_ref(v_str_1609_);
lean_dec_ref(v_str_1608_);
lean_dec(v_addDeclName_1544_);
lean_dec(v_declName_1542_);
v___y_1585_ = v___y_1599_;
v___y_1586_ = v_a_1545_;
v___y_1587_ = v_a_1546_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_921759773____hygCtx___hyg_2_));
v___x_1615_ = lean_string_dec_eq(v_str_1610_, v___x_1614_);
lean_dec_ref(v_str_1610_);
if (v___x_1615_ == 0)
{
lean_dec_ref(v_str_1609_);
lean_dec_ref(v_str_1608_);
lean_dec(v_addDeclName_1544_);
lean_dec(v_declName_1542_);
v___y_1585_ = v___y_1599_;
v___y_1586_ = v_a_1545_;
v___y_1587_ = v_a_1546_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1616_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__11));
v___x_1617_ = lean_string_dec_eq(v_str_1609_, v___x_1616_);
lean_dec_ref(v_str_1609_);
if (v___x_1617_ == 0)
{
lean_dec_ref(v_str_1608_);
lean_dec(v_addDeclName_1544_);
lean_dec(v_declName_1542_);
v___y_1585_ = v___y_1599_;
v___y_1586_ = v_a_1545_;
v___y_1587_ = v_a_1546_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__12));
v___x_1619_ = lean_string_dec_eq(v_str_1608_, v___x_1618_);
lean_dec_ref(v_str_1608_);
if (v___x_1619_ == 0)
{
lean_dec(v_addDeclName_1544_);
lean_dec(v_declName_1542_);
v___y_1585_ = v___y_1599_;
v___y_1586_ = v_a_1545_;
v___y_1587_ = v_a_1546_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1620_ = lean_box(0);
v___x_1621_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__19);
v___x_1622_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__21);
v___x_1623_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24_once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___closed__24);
lean_inc(v_declName_1542_);
v___x_1624_ = l_Lean_mkConst(v_declName_1542_, v___x_1620_);
v___x_1625_ = l_Lean_mkApp3(v___x_1621_, v___x_1622_, v___x_1623_, v___x_1624_);
v___y_1575_ = v___y_1599_;
v_procExpr_1576_ = v___x_1625_;
v___y_1577_ = v_a_1545_;
v___y_1578_ = v_a_1546_;
goto v___jp_1574_;
}
}
}
}
}
else
{
lean_dec_ref(v_pre_1606_);
lean_dec_ref(v_pre_1605_);
lean_dec_ref(v_pre_1604_);
lean_dec_ref(v_declName_1603_);
lean_dec(v_addDeclName_1544_);
lean_dec(v_declName_1542_);
v___y_1585_ = v___y_1599_;
v___y_1586_ = v_a_1545_;
v___y_1587_ = v_a_1546_;
goto v___jp_1584_;
}
}
else
{
lean_dec_ref(v_pre_1605_);
lean_dec(v_pre_1606_);
lean_dec_ref(v_pre_1604_);
lean_dec_ref(v_declName_1603_);
lean_dec(v_addDeclName_1544_);
lean_dec(v_declName_1542_);
v___y_1585_ = v___y_1599_;
v___y_1586_ = v_a_1545_;
v___y_1587_ = v_a_1546_;
goto v___jp_1584_;
}
}
else
{
lean_dec(v_pre_1605_);
lean_dec_ref(v_pre_1604_);
lean_dec_ref(v_declName_1603_);
lean_dec(v_addDeclName_1544_);
lean_dec(v_declName_1542_);
v___y_1585_ = v___y_1599_;
v___y_1586_ = v_a_1545_;
v___y_1587_ = v_a_1546_;
goto v___jp_1584_;
}
}
else
{
lean_dec_ref(v_declName_1603_);
lean_dec(v_pre_1604_);
lean_dec(v_addDeclName_1544_);
lean_dec(v_declName_1542_);
v___y_1585_ = v___y_1599_;
v___y_1586_ = v_a_1545_;
v___y_1587_ = v_a_1546_;
goto v___jp_1584_;
}
}
else
{
lean_dec(v_declName_1603_);
lean_dec(v_addDeclName_1544_);
lean_dec(v_declName_1542_);
v___y_1585_ = v___y_1599_;
v___y_1586_ = v_a_1545_;
v___y_1587_ = v_a_1546_;
goto v___jp_1584_;
}
}
else
{
lean_dec_ref(v___x_1602_);
lean_dec(v_addDeclName_1544_);
lean_dec(v_declName_1542_);
v___y_1585_ = v___y_1599_;
v___y_1586_ = v_a_1545_;
v___y_1587_ = v_a_1546_;
goto v___jp_1584_;
}
}
else
{
lean_object* v_a_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1633_; 
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
lean_dec(v_addDeclName_1544_);
lean_dec(v_declName_1542_);
v_a_1626_ = lean_ctor_get(v___x_1600_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1600_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1628_ = v___x_1600_;
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_a_1626_);
lean_dec(v___x_1600_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1633_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1631_; 
if (v_isShared_1629_ == 0)
{
v___x_1631_ = v___x_1628_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_a_1626_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin___boxed(lean_object* v_declName_1642_, lean_object* v_stx_1643_, lean_object* v_addDeclName_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin(v_declName_1642_, v_stx_1643_, v_addDeclName_1644_, v_a_1645_, v_a_1646_);
lean_dec(v_stx_1643_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0(lean_object* v_00_u03b1_1649_, lean_object* v_msg_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(v_msg_1650_, v___y_1651_, v___y_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___boxed(lean_object* v_00_u03b1_1655_, lean_object* v_msg_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0(v_00_u03b1_1655_, v_msg_1656_, v___y_1657_, v___y_1658_);
lean_dec(v___y_1658_);
lean_dec_ref(v___y_1657_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2(lean_object* v_00_u03b1_1661_, lean_object* v_constName_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___redArg(v_constName_1662_, v___y_1663_, v___y_1664_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1667_, lean_object* v_constName_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2(v_00_u03b1_1667_, v_constName_1668_, v___y_1669_, v___y_1670_);
lean_dec(v___y_1670_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3(lean_object* v_00_u03b1_1673_, lean_object* v_ref_1674_, lean_object* v_constName_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___redArg(v_ref_1674_, v_constName_1675_, v___y_1676_, v___y_1677_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1680_, lean_object* v_ref_1681_, lean_object* v_constName_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3(v_00_u03b1_1680_, v_ref_1681_, v_constName_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec(v_ref_1681_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4(lean_object* v_00_u03b1_1687_, lean_object* v_ref_1688_, lean_object* v_msg_1689_, lean_object* v_declHint_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___redArg(v_ref_1688_, v_msg_1689_, v_declHint_1690_, v___y_1691_, v___y_1692_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1695_, lean_object* v_ref_1696_, lean_object* v_msg_1697_, lean_object* v_declHint_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4(v_00_u03b1_1695_, v_ref_1696_, v_msg_1697_, v_declHint_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec(v_ref_1696_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(lean_object* v_msg_1703_, lean_object* v_declHint_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_msg_1703_, v_declHint_1704_, v___y_1706_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6___boxed(lean_object* v_msg_1709_, lean_object* v_declHint_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__5_spec__6(v_msg_1709_, v_declHint_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6(lean_object* v_00_u03b1_1715_, lean_object* v_ref_1716_, lean_object* v_msg_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___redArg(v_ref_1716_, v_msg_1717_, v___y_1718_, v___y_1719_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_ref_1723_, lean_object* v_msg_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__1_spec__2_spec__3_spec__4_spec__6(v_00_u03b1_1722_, v_ref_1723_, v_msg_1724_, v___y_1725_, v___y_1726_);
lean_dec(v___y_1726_);
lean_dec(v_ref_1723_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr(lean_object* v_declName_1729_, uint8_t v_post_1730_, lean_object* v_proc_1731_){
_start:
{
lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1733_ = l_Lean_Elab_Tactic_BVDecide_Frontend_builtinBVNormalizeSimprocsRef;
v___x_1734_ = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(v___x_1733_, v_declName_1729_, v_post_1730_, v_proc_1731_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr___boxed(lean_object* v_declName_1735_, lean_object* v_post_1736_, lean_object* v_proc_1737_, lean_object* v_a_1738_){
_start:
{
uint8_t v_post_boxed_1739_; lean_object* v_res_1740_; 
v_post_boxed_1739_ = lean_unbox(v_post_1736_);
v_res_1740_ = l_Lean_Elab_Tactic_BVDecide_Frontend_addBVNormalizeProcBuiltinAttr(v_declName_1735_, v_post_boxed_1739_, v_proc_1737_);
return v_res_1740_;
}
}
static lean_object* _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1742_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_));
v___x_1743_ = l_Lean_stringToMessageData(v___x_1742_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(lean_object* v_x_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1748_ = lean_obj_once(&l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_, &l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2__once, _init_l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0___closed__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_);
v___x_1749_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin_spec__0___redArg(v___x_1748_, v___y_1745_, v___y_1746_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed(lean_object* v_x_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(v_x_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v_x_1750_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(lean_object* v___x_1756_, lean_object* v___x_1757_, lean_object* v___x_1758_, lean_object* v___x_1759_, lean_object* v___x_1760_, lean_object* v_declName_1761_, lean_object* v_stx_1762_, uint8_t v_x_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1___closed__0_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_));
v___x_1768_ = l_Lean_Name_mkStr6(v___x_1756_, v___x_1757_, v___x_1758_, v___x_1759_, v___x_1760_, v___x_1767_);
v___x_1769_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_addBuiltin(v_declName_1761_, v_stx_1762_, v___x_1768_, v___y_1764_, v___y_1765_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed(lean_object* v___x_1770_, lean_object* v___x_1771_, lean_object* v___x_1772_, lean_object* v___x_1773_, lean_object* v___x_1774_, lean_object* v_declName_1775_, lean_object* v_stx_1776_, lean_object* v_x_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
uint8_t v_x_164__boxed_1781_; lean_object* v_res_1782_; 
v_x_164__boxed_1781_ = lean_unbox(v_x_1777_);
v_res_1782_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___lam__1_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(v___x_1770_, v___x_1771_, v___x_1772_, v___x_1773_, v___x_1774_, v_declName_1775_, v_stx_1776_, v_x_164__boxed_1781_, v___y_1778_, v___y_1779_);
lean_dec(v_stx_1776_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn___closed__10_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_));
v___x_1817_ = l_Lean_registerBuiltinAttribute(v___x_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2____boxed(lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l___private_Lean_Elab_Tactic_BVDecide_Frontend_Attr_0__Lean_Elab_Tactic_BVDecide_Frontend_initFn_00___x40_Lean_Elab_Tactic_BVDecide_Frontend_Attr_1596612692____hygCtx___hyg_2_();
return v_res_1819_;
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
