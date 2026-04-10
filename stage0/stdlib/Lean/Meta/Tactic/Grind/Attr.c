// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Attr
// Imports: public import Lean.Meta.Tactic.Grind.Injective public import Lean.Meta.Tactic.Grind.Cases public import Lean.Meta.Tactic.Grind.ExtAttr public import Lean.Meta.Tactic.Simp.Attr import Lean.ExtraModUses
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
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instInhabitedExtensionState_default;
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_Meta_Grind_Theorems_contains___redArg(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ExtTheorems_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_ensureNotBuiltinCases(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_CasesTypes_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkExtension(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSimpExt(lean_object*);
lean_object* l_Lean_Meta_addDeclToUnfold(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addEMatchAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateCasesAttr(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_validateExtAttr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addSymbolPriorityAttr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Extension_addInjectiveAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_CasesTypes_isSplit(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "normExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 117, 24, 11, 244, 218, 170, 88)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindMod"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 252, 83, 80, 136, 168, 19, 119)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "unexpected `grind` theorem kind: `"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__5;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__7;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindEq"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(179, 34, 219, 24, 240, 38, 65, 204)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindDef"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value),LEAN_SCALAR_PTR_LITERAL(66, 218, 12, 28, 39, 29, 4, 77)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindFwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value),LEAN_SCALAR_PTR_LITERAL(121, 161, 177, 116, 112, 162, 92, 47)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value),LEAN_SCALAR_PTR_LITERAL(114, 163, 57, 243, 160, 41, 114, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqRhs"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value),LEAN_SCALAR_PTR_LITERAL(222, 187, 148, 221, 105, 213, 199, 68)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindEqBoth"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value),LEAN_SCALAR_PTR_LITERAL(79, 230, 133, 190, 186, 228, 109, 128)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value),LEAN_SCALAR_PTR_LITERAL(250, 57, 23, 180, 238, 116, 90, 53)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindLR"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value),LEAN_SCALAR_PTR_LITERAL(152, 111, 188, 78, 132, 212, 97, 164)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindRL"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value),LEAN_SCALAR_PTR_LITERAL(84, 112, 237, 169, 105, 148, 42, 205)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindUsr"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value),LEAN_SCALAR_PTR_LITERAL(204, 58, 160, 148, 192, 167, 114, 18)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindGen"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value),LEAN_SCALAR_PTR_LITERAL(186, 203, 120, 147, 97, 215, 208, 134)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindCases"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value),LEAN_SCALAR_PTR_LITERAL(85, 142, 28, 230, 49, 50, 229, 162)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "grindCasesEager"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value),LEAN_SCALAR_PTR_LITERAL(75, 210, 92, 40, 190, 183, 142, 70)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindIntro"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value),LEAN_SCALAR_PTR_LITERAL(142, 126, 114, 89, 237, 253, 56, 138)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindExt"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value),LEAN_SCALAR_PTR_LITERAL(147, 193, 153, 166, 243, 149, 163, 253)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindInj"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value),LEAN_SCALAR_PTR_LITERAL(223, 225, 41, 9, 21, 5, 145, 193)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__39 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindFunCC"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value),LEAN_SCALAR_PTR_LITERAL(217, 20, 186, 134, 249, 79, 78, 43)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__41 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindNorm"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__42 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value),LEAN_SCALAR_PTR_LITERAL(166, 126, 146, 239, 104, 253, 29, 148)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__43 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindUnfold"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__44 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value),LEAN_SCALAR_PTR_LITERAL(214, 181, 37, 92, 122, 232, 164, 219)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__45 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSym"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value),LEAN_SCALAR_PTR_LITERAL(104, 204, 11, 169, 55, 109, 254, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__47 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__47_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "priority expected"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__48 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__48_value;
static lean_once_cell_t l_Lean_Meta_Grind_getAttrKindCore___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__49;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__50 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "simpPost"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__51 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__52 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__53 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__54_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__54_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value),LEAN_SCALAR_PTR_LITERAL(197, 59, 48, 6, 36, 81, 149, 152)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__54 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__54_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(9) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__55 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__55_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__56 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__56_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(6) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__57 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__57_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__58 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__58_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__59 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__59_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__60 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__60_value)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__61 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__61_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "the modifier `usr` is only relevant in parameters for `grind only`"};
static const lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "declName"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(113, 211, 58, 33, 138, 196, 138, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "decl_name%"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 24, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 1, 1, 0),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 1, 1, 1, 2, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "\?]` is a helper attribute for displaying inferred patterns, if you want to remove the attribute, consider using `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "]` instead"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 8}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "cannot mark declaration to be unfolded by `grind`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "invalid `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = " intro]`, `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "` is not an inductive predicate"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "symbol priorities must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "normalizer must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 72, .m_capacity = 72, .m_length = 71, .m_data = "declaration to unfold must be set using the default `[grind]` attribute"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "When applied to an equational theorem, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " =]`, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = " =_]`, or `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = " _=_]`will mark the theorem for use in heuristic instantiations by the `"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 136, .m_capacity = 136, .m_length = 135, .m_data = "` tactic,\n      using respectively the left-hand side, the right-hand side, or both sides of the theorem.When applied to a function, `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 112, .m_capacity = 112, .m_length = 111, .m_data = " =]` automatically annotates the equational theorems associated with that function.When applied to a theorem `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 183, .m_capacity = 183, .m_length = 180, .m_data = " ←]` will instantiate the theorem whenever it encounters the conclusion of the theorem\n      (that is, it will use the theorem for backwards reasoning).When applied to a theorem `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 190, .m_capacity = 190, .m_length = 187, .m_data = " →]` will instantiate the theorem whenever it encounters sufficiently many of the propositional hypotheses\n      (that is, it will use the theorem for forwards reasoning).The attribute `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "]` by itself will effectively try `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 68, .m_data = " ←]` (if the conclusion is sufficient for instantiation) and then `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 165, .m_capacity = 165, .m_length = 162, .m_data = " →]`.The `grind` tactic utilizes annotated theorems to add instances of matching patterns into the local context during proof search.For example, if a theorem `@["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 179, .m_capacity = 179, .m_length = 178, .m_data = " =] theorem foo_idempotent : foo (foo x) = foo x` is annotated,`grind` will add an instance of this theorem to the local context whenever it encounters the pattern `foo (foo x)`."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "The `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "]` attribute is used to annotate declarations."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "\?]` attribute is identical to the `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 57, .m_capacity = 57, .m_length = 56, .m_data = "]` attribute, but displays inferred pattern information."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 90, .m_capacity = 90, .m_length = 89, .m_data = "!]` attribute is used to annotate declarations, but selecting minimal indexable subterms."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "!\?]` attribute is identical to the `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "!]` attribute, but displays inferred pattern information."};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "!"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!\?"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_extensionMapRef;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___auto__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value),LEAN_SCALAR_PTR_LITERAL(160, 1, 171, 211, 177, 132, 129, 49)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_grindExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_));
v___x_12_ = l_Lean_Meta_mkSimpExt(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx(lean_object* v_x_15_){
_start:
{
switch(lean_obj_tag(v_x_15_))
{
case 0:
{
lean_object* v___x_16_; 
v___x_16_ = lean_unsigned_to_nat(0u);
return v___x_16_;
}
case 1:
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(1u);
return v___x_17_;
}
case 2:
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(2u);
return v___x_18_;
}
case 3:
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(3u);
return v___x_19_;
}
case 4:
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(4u);
return v___x_20_;
}
case 5:
{
lean_object* v___x_21_; 
v___x_21_ = lean_unsigned_to_nat(5u);
return v___x_21_;
}
case 6:
{
lean_object* v___x_22_; 
v___x_22_ = lean_unsigned_to_nat(6u);
return v___x_22_;
}
case 7:
{
lean_object* v___x_23_; 
v___x_23_ = lean_unsigned_to_nat(7u);
return v___x_23_;
}
case 8:
{
lean_object* v___x_24_; 
v___x_24_ = lean_unsigned_to_nat(8u);
return v___x_24_;
}
default: 
{
lean_object* v___x_25_; 
v___x_25_ = lean_unsigned_to_nat(9u);
return v___x_25_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorIdx___boxed(lean_object* v_x_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_Meta_Grind_AttrKind_ctorIdx(v_x_26_);
lean_dec(v_x_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(lean_object* v_t_28_, lean_object* v_k_29_){
_start:
{
switch(lean_obj_tag(v_t_28_))
{
case 0:
{
lean_object* v_k_30_; lean_object* v___x_31_; 
v_k_30_ = lean_ctor_get(v_t_28_, 0);
lean_inc(v_k_30_);
lean_dec_ref(v_t_28_);
v___x_31_ = lean_apply_1(v_k_29_, v_k_30_);
return v___x_31_;
}
case 1:
{
uint8_t v_eager_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_eager_32_ = lean_ctor_get_uint8(v_t_28_, 0);
lean_dec_ref(v_t_28_);
v___x_33_ = lean_box(v_eager_32_);
v___x_34_ = lean_apply_1(v_k_29_, v___x_33_);
return v___x_34_;
}
case 5:
{
lean_object* v_prio_35_; lean_object* v___x_36_; 
v_prio_35_ = lean_ctor_get(v_t_28_, 0);
lean_inc(v_prio_35_);
lean_dec_ref(v_t_28_);
v___x_36_ = lean_apply_1(v_k_29_, v_prio_35_);
return v___x_36_;
}
case 8:
{
uint8_t v_post_37_; uint8_t v_inv_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v_post_37_ = lean_ctor_get_uint8(v_t_28_, 0);
v_inv_38_ = lean_ctor_get_uint8(v_t_28_, 1);
lean_dec_ref(v_t_28_);
v___x_39_ = lean_box(v_post_37_);
v___x_40_ = lean_box(v_inv_38_);
v___x_41_ = lean_apply_2(v_k_29_, v___x_39_, v___x_40_);
return v___x_41_;
}
default: 
{
lean_dec(v_t_28_);
return v_k_29_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim(lean_object* v_motive_42_, lean_object* v_ctorIdx_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_k_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_44_, v_k_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ctorElim___boxed(lean_object* v_motive_48_, lean_object* v_ctorIdx_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_k_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Meta_Grind_AttrKind_ctorElim(v_motive_48_, v_ctorIdx_49_, v_t_50_, v_h_51_, v_k_52_);
lean_dec(v_ctorIdx_49_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim___redArg(lean_object* v_t_54_, lean_object* v_ematch_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_54_, v_ematch_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ematch_elim(lean_object* v_motive_57_, lean_object* v_t_58_, lean_object* v_h_59_, lean_object* v_ematch_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_58_, v_ematch_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim___redArg(lean_object* v_t_62_, lean_object* v_cases_63_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_62_, v_cases_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_cases_elim(lean_object* v_motive_65_, lean_object* v_t_66_, lean_object* v_h_67_, lean_object* v_cases_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_66_, v_cases_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim___redArg(lean_object* v_t_70_, lean_object* v_intro_71_){
_start:
{
lean_object* v___x_72_; 
v___x_72_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_70_, v_intro_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_intro_elim(lean_object* v_motive_73_, lean_object* v_t_74_, lean_object* v_h_75_, lean_object* v_intro_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_74_, v_intro_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim___redArg(lean_object* v_t_78_, lean_object* v_infer_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_78_, v_infer_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_infer_elim(lean_object* v_motive_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_infer_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_82_, v_infer_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim___redArg(lean_object* v_t_86_, lean_object* v_ext_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_86_, v_ext_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_ext_elim(lean_object* v_motive_89_, lean_object* v_t_90_, lean_object* v_h_91_, lean_object* v_ext_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_90_, v_ext_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim___redArg(lean_object* v_t_94_, lean_object* v_symbol_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_94_, v_symbol_95_);
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_symbol_elim(lean_object* v_motive_97_, lean_object* v_t_98_, lean_object* v_h_99_, lean_object* v_symbol_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_98_, v_symbol_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim___redArg(lean_object* v_t_102_, lean_object* v_inj_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_102_, v_inj_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_inj_elim(lean_object* v_motive_105_, lean_object* v_t_106_, lean_object* v_h_107_, lean_object* v_inj_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_106_, v_inj_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim___redArg(lean_object* v_t_110_, lean_object* v_funCC_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_110_, v_funCC_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_funCC_elim(lean_object* v_motive_113_, lean_object* v_t_114_, lean_object* v_h_115_, lean_object* v_funCC_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_114_, v_funCC_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim___redArg(lean_object* v_t_118_, lean_object* v_norm_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_118_, v_norm_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_norm_elim(lean_object* v_motive_121_, lean_object* v_t_122_, lean_object* v_h_123_, lean_object* v_norm_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_122_, v_norm_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim___redArg(lean_object* v_t_126_, lean_object* v_unfold_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_126_, v_unfold_127_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AttrKind_unfold_elim(lean_object* v_motive_129_, lean_object* v_t_130_, lean_object* v_h_131_, lean_object* v_unfold_132_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_Meta_Grind_AttrKind_ctorElim___redArg(v_t_130_, v_unfold_132_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_134_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_135_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__0);
v___x_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
return v___x_136_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
lean_ctor_set(v___x_139_, 2, v___x_138_);
lean_ctor_set(v___x_139_, 3, v___x_138_);
lean_ctor_set(v___x_139_, 4, v___x_137_);
lean_ctor_set(v___x_139_, 5, v___x_137_);
lean_ctor_set(v___x_139_, 6, v___x_137_);
lean_ctor_set(v___x_139_, 7, v___x_137_);
lean_ctor_set(v___x_139_, 8, v___x_137_);
lean_ctor_set(v___x_139_, 9, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_unsigned_to_nat(32u);
v___x_141_ = lean_mk_empty_array_with_capacity(v___x_140_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_143_ = ((size_t)5ULL);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_unsigned_to_nat(32u);
v___x_146_ = lean_mk_empty_array_with_capacity(v___x_145_);
v___x_147_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__3);
v___x_148_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v___x_146_);
lean_ctor_set(v___x_148_, 2, v___x_144_);
lean_ctor_set(v___x_148_, 3, v___x_144_);
lean_ctor_set_usize(v___x_148_, 4, v___x_143_);
return v___x_148_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_149_ = lean_box(1);
v___x_150_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_151_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__1);
v___x_152_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v___x_150_);
lean_ctor_set(v___x_152_, 2, v___x_149_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(lean_object* v_msgData_153_, lean_object* v___y_154_, lean_object* v___y_155_){
_start:
{
lean_object* v___x_157_; lean_object* v_env_158_; lean_object* v_options_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_157_ = lean_st_ref_get(v___y_155_);
v_env_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc_ref(v_env_158_);
lean_dec(v___x_157_);
v_options_159_ = lean_ctor_get(v___y_154_, 2);
v___x_160_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__2);
v___x_161_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_159_);
v___x_162_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_162_, 0, v_env_158_);
lean_ctor_set(v___x_162_, 1, v___x_160_);
lean_ctor_set(v___x_162_, 2, v___x_161_);
lean_ctor_set(v___x_162_, 3, v_options_159_);
v___x_163_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v_msgData_153_);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___boxed(lean_object* v_msgData_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msgData_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(lean_object* v_msg_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_ref_174_; lean_object* v___x_175_; lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_184_; 
v_ref_174_ = lean_ctor_get(v___y_171_, 5);
v___x_175_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_170_, v___y_171_, v___y_172_);
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_184_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_184_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_182_; 
lean_inc(v_ref_174_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_ref_174_);
lean_ctor_set(v___x_180_, 1, v_a_176_);
if (v_isShared_179_ == 0)
{
lean_ctor_set_tag(v___x_178_, 1);
lean_ctor_set(v___x_178_, 0, v___x_180_);
v___x_182_ = v___x_178_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg___boxed(lean_object* v_msg_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(lean_object* v_ref_190_, lean_object* v_msg_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_fileName_195_; lean_object* v_fileMap_196_; lean_object* v_options_197_; lean_object* v_currRecDepth_198_; lean_object* v_maxRecDepth_199_; lean_object* v_ref_200_; lean_object* v_currNamespace_201_; lean_object* v_openDecls_202_; lean_object* v_initHeartbeats_203_; lean_object* v_maxHeartbeats_204_; lean_object* v_quotContext_205_; lean_object* v_currMacroScope_206_; uint8_t v_diag_207_; lean_object* v_cancelTk_x3f_208_; uint8_t v_suppressElabErrors_209_; lean_object* v_inheritedTraceOptions_210_; lean_object* v_ref_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_fileName_195_ = lean_ctor_get(v___y_192_, 0);
v_fileMap_196_ = lean_ctor_get(v___y_192_, 1);
v_options_197_ = lean_ctor_get(v___y_192_, 2);
v_currRecDepth_198_ = lean_ctor_get(v___y_192_, 3);
v_maxRecDepth_199_ = lean_ctor_get(v___y_192_, 4);
v_ref_200_ = lean_ctor_get(v___y_192_, 5);
v_currNamespace_201_ = lean_ctor_get(v___y_192_, 6);
v_openDecls_202_ = lean_ctor_get(v___y_192_, 7);
v_initHeartbeats_203_ = lean_ctor_get(v___y_192_, 8);
v_maxHeartbeats_204_ = lean_ctor_get(v___y_192_, 9);
v_quotContext_205_ = lean_ctor_get(v___y_192_, 10);
v_currMacroScope_206_ = lean_ctor_get(v___y_192_, 11);
v_diag_207_ = lean_ctor_get_uint8(v___y_192_, sizeof(void*)*14);
v_cancelTk_x3f_208_ = lean_ctor_get(v___y_192_, 12);
v_suppressElabErrors_209_ = lean_ctor_get_uint8(v___y_192_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_210_ = lean_ctor_get(v___y_192_, 13);
v_ref_211_ = l_Lean_replaceRef(v_ref_190_, v_ref_200_);
lean_inc_ref(v_inheritedTraceOptions_210_);
lean_inc(v_cancelTk_x3f_208_);
lean_inc(v_currMacroScope_206_);
lean_inc(v_quotContext_205_);
lean_inc(v_maxHeartbeats_204_);
lean_inc(v_initHeartbeats_203_);
lean_inc(v_openDecls_202_);
lean_inc(v_currNamespace_201_);
lean_inc(v_maxRecDepth_199_);
lean_inc(v_currRecDepth_198_);
lean_inc_ref(v_options_197_);
lean_inc_ref(v_fileMap_196_);
lean_inc_ref(v_fileName_195_);
v___x_212_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_212_, 0, v_fileName_195_);
lean_ctor_set(v___x_212_, 1, v_fileMap_196_);
lean_ctor_set(v___x_212_, 2, v_options_197_);
lean_ctor_set(v___x_212_, 3, v_currRecDepth_198_);
lean_ctor_set(v___x_212_, 4, v_maxRecDepth_199_);
lean_ctor_set(v___x_212_, 5, v_ref_211_);
lean_ctor_set(v___x_212_, 6, v_currNamespace_201_);
lean_ctor_set(v___x_212_, 7, v_openDecls_202_);
lean_ctor_set(v___x_212_, 8, v_initHeartbeats_203_);
lean_ctor_set(v___x_212_, 9, v_maxHeartbeats_204_);
lean_ctor_set(v___x_212_, 10, v_quotContext_205_);
lean_ctor_set(v___x_212_, 11, v_currMacroScope_206_);
lean_ctor_set(v___x_212_, 12, v_cancelTk_x3f_208_);
lean_ctor_set(v___x_212_, 13, v_inheritedTraceOptions_210_);
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*14, v_diag_207_);
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*14 + 1, v_suppressElabErrors_209_);
v___x_213_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_191_, v___x_212_, v___y_193_);
lean_dec_ref(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object* v_ref_214_, lean_object* v_msg_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_214_, v_msg_215_, v___y_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v_ref_214_);
return v_res_219_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5(void){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__4));
v___x_230_ = l_Lean_stringToMessageData(v___x_229_);
return v___x_230_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_232_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__6));
v___x_233_ = l_Lean_stringToMessageData(v___x_232_);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__49(void){
_start:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_355_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__48));
v___x_356_ = l_Lean_stringToMessageData(v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object* v_stx_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_388_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__3));
lean_inc(v_stx_384_);
v___x_389_ = l_Lean_Syntax_isOfKind(v_stx_384_, v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_390_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_391_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_392_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_390_);
lean_ctor_set(v___x_392_, 1, v___x_391_);
v___x_393_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_394_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_392_);
lean_ctor_set(v___x_394_, 1, v___x_393_);
v___x_395_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_394_, v_a_385_, v_a_386_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = l_Lean_Syntax_getArg(v_stx_384_, v___x_396_);
v___x_398_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__9));
lean_inc(v___x_397_);
v___x_399_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__11));
lean_inc(v___x_397_);
v___x_401_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_402_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__13));
lean_inc(v___x_397_);
v___x_403_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__15));
lean_inc(v___x_397_);
v___x_405_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__17));
lean_inc(v___x_397_);
v___x_407_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__19));
lean_inc(v___x_397_);
v___x_409_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__21));
lean_inc(v___x_397_);
v___x_411_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__23));
lean_inc(v___x_397_);
v___x_413_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__25));
lean_inc(v___x_397_);
v___x_415_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__27));
lean_inc(v___x_397_);
v___x_417_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
lean_inc(v___x_397_);
v___x_419_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__31));
lean_inc(v___x_397_);
v___x_421_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__33));
lean_inc(v___x_397_);
v___x_423_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__35));
lean_inc(v___x_397_);
v___x_425_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__37));
lean_inc(v___x_397_);
v___x_427_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__39));
lean_inc(v___x_397_);
v___x_429_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__41));
lean_inc(v___x_397_);
v___x_431_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__43));
lean_inc(v___x_397_);
v___x_433_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__45));
lean_inc(v___x_397_);
v___x_435_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__47));
lean_inc(v___x_397_);
v___x_437_ = l_Lean_Syntax_isOfKind(v___x_397_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
lean_dec(v___x_397_);
v___x_438_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_439_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_440_);
lean_ctor_set(v___x_442_, 1, v___x_441_);
v___x_443_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_442_, v_a_385_, v_a_386_);
return v___x_443_;
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
lean_dec(v_stx_384_);
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = l_Lean_Syntax_getArg(v___x_397_, v___x_444_);
lean_dec(v___x_397_);
v___x_446_ = l_Lean_Syntax_isNatLit_x3f(v___x_445_);
if (lean_obj_tag(v___x_446_) == 1)
{
lean_object* v_val_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_455_; 
lean_dec(v___x_445_);
v_val_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_455_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_val_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_455_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set_tag(v___x_449_, 5);
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_val_447_);
v___x_452_ = v_reuseFailAlloc_454_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; 
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v___x_446_);
v___x_456_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__49, &l_Lean_Meta_Grind_getAttrKindCore___closed__49_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__49);
v___x_457_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v___x_445_, v___x_456_, v_a_385_, v_a_386_);
lean_dec(v___x_445_);
return v___x_457_;
}
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_459_; 
lean_dec(v___x_397_);
lean_dec(v_stx_384_);
v___x_458_ = lean_box(9);
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = l_Lean_Syntax_getArg(v___x_397_, v___x_460_);
lean_inc(v___x_461_);
v___x_462_ = l_Lean_Syntax_matchesNull(v___x_461_, v___x_396_);
if (v___x_462_ == 0)
{
uint8_t v___x_463_; 
lean_inc(v___x_461_);
v___x_463_ = l_Lean_Syntax_matchesNull(v___x_461_, v___x_460_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
lean_dec(v___x_461_);
lean_dec(v___x_397_);
v___x_464_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_465_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_466_, 0, v___x_464_);
lean_ctor_set(v___x_466_, 1, v___x_465_);
v___x_467_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_466_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
v___x_469_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_468_, v_a_385_, v_a_386_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_470_ = l_Lean_Syntax_getArg(v___x_461_, v___x_396_);
lean_dec(v___x_461_);
v___x_471_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__52));
lean_inc(v___x_470_);
v___x_472_ = l_Lean_Syntax_isOfKind(v___x_470_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__54));
v___x_474_ = l_Lean_Syntax_isOfKind(v___x_470_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec(v___x_397_);
v___x_475_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_476_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_475_);
lean_ctor_set(v___x_477_, 1, v___x_476_);
v___x_478_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_477_);
lean_ctor_set(v___x_479_, 1, v___x_478_);
v___x_480_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_479_, v_a_385_, v_a_386_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_481_ = lean_unsigned_to_nat(2u);
v___x_482_ = l_Lean_Syntax_getArg(v___x_397_, v___x_481_);
lean_dec(v___x_397_);
lean_inc(v___x_482_);
v___x_483_ = l_Lean_Syntax_matchesNull(v___x_482_, v___x_396_);
if (v___x_483_ == 0)
{
uint8_t v___x_484_; 
v___x_484_ = l_Lean_Syntax_matchesNull(v___x_482_, v___x_460_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_485_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_486_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_489_, v_a_385_, v_a_386_);
return v___x_490_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v_stx_384_);
v___x_491_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_491_, 0, v___x_483_);
lean_ctor_set_uint8(v___x_491_, 1, v___x_389_);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
}
else
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_dec(v___x_482_);
lean_dec(v_stx_384_);
v___x_493_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_493_, 0, v___x_472_);
lean_ctor_set_uint8(v___x_493_, 1, v___x_472_);
v___x_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
return v___x_494_;
}
}
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
lean_dec(v___x_470_);
v___x_495_ = lean_unsigned_to_nat(2u);
v___x_496_ = l_Lean_Syntax_getArg(v___x_397_, v___x_495_);
lean_dec(v___x_397_);
lean_inc(v___x_496_);
v___x_497_ = l_Lean_Syntax_matchesNull(v___x_496_, v___x_396_);
if (v___x_497_ == 0)
{
uint8_t v___x_498_; 
v___x_498_ = l_Lean_Syntax_matchesNull(v___x_496_, v___x_460_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_499_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_500_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_499_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v___x_502_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_501_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_503_, v_a_385_, v_a_386_);
return v___x_504_;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; 
lean_dec(v_stx_384_);
v___x_505_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_505_, 0, v___x_389_);
lean_ctor_set_uint8(v___x_505_, 1, v___x_389_);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec(v___x_496_);
lean_dec(v_stx_384_);
v___x_507_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_507_, 0, v___x_389_);
lean_ctor_set_uint8(v___x_507_, 1, v___x_462_);
v___x_508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
return v___x_508_;
}
}
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
lean_dec(v___x_461_);
v___x_509_ = lean_unsigned_to_nat(2u);
v___x_510_ = l_Lean_Syntax_getArg(v___x_397_, v___x_509_);
lean_dec(v___x_397_);
lean_inc(v___x_510_);
v___x_511_ = l_Lean_Syntax_matchesNull(v___x_510_, v___x_396_);
if (v___x_511_ == 0)
{
uint8_t v___x_512_; 
v___x_512_ = l_Lean_Syntax_matchesNull(v___x_510_, v___x_460_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_513_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_514_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
v___x_516_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_515_);
lean_ctor_set(v___x_517_, 1, v___x_516_);
v___x_518_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_517_, v_a_385_, v_a_386_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec(v_stx_384_);
v___x_519_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_519_, 0, v___x_389_);
lean_ctor_set_uint8(v___x_519_, 1, v___x_389_);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec(v___x_510_);
lean_dec(v_stx_384_);
v___x_521_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_521_, 0, v___x_389_);
lean_ctor_set_uint8(v___x_521_, 1, v___x_431_);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
}
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec(v___x_397_);
lean_dec(v_stx_384_);
v___x_523_ = lean_box(7);
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; 
lean_dec(v___x_397_);
lean_dec(v_stx_384_);
v___x_525_ = lean_box(6);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v___x_397_);
lean_dec(v_stx_384_);
v___x_527_ = lean_box(4);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v___x_397_);
lean_dec(v_stx_384_);
v___x_529_ = lean_box(2);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v___x_397_);
lean_dec(v_stx_384_);
v___x_531_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_531_, 0, v___x_389_);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec(v___x_397_);
lean_dec(v_stx_384_);
v___x_533_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_533_, 0, v___x_419_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec(v___x_397_);
lean_dec(v_stx_384_);
v___x_535_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_535_, 0, v___x_389_);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
v___x_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
return v___x_537_;
}
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; 
lean_dec(v___x_397_);
lean_dec(v_stx_384_);
v___x_538_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__55));
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
return v___x_539_;
}
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; 
lean_dec(v___x_397_);
lean_dec(v_stx_384_);
v___x_540_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__56));
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
else
{
lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec(v___x_397_);
lean_dec(v_stx_384_);
v___x_542_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__57));
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v___x_397_);
lean_dec(v_stx_384_);
v___x_544_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__58));
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; uint8_t v___x_548_; 
v___x_546_ = lean_unsigned_to_nat(3u);
v___x_547_ = l_Lean_Syntax_getArg(v___x_397_, v___x_546_);
lean_dec(v___x_397_);
lean_inc(v___x_547_);
v___x_548_ = l_Lean_Syntax_matchesNull(v___x_547_, v___x_396_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_547_);
v___x_550_ = l_Lean_Syntax_matchesNull(v___x_547_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_dec(v___x_547_);
v___x_551_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_552_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_551_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
v___x_554_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_553_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
v___x_556_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_555_, v_a_385_, v_a_386_);
return v___x_556_;
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v___x_557_ = l_Lean_Syntax_getArg(v___x_547_, v___x_396_);
lean_dec(v___x_547_);
v___x_558_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_559_ = l_Lean_Syntax_isOfKind(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_560_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_561_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_560_);
lean_ctor_set(v___x_562_, 1, v___x_561_);
v___x_563_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_564_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_562_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
v___x_565_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_564_, v_a_385_, v_a_386_);
return v___x_565_;
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec(v_stx_384_);
v___x_566_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_566_, 0, v___x_389_);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
v___x_568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
return v___x_568_;
}
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v___x_547_);
lean_dec(v_stx_384_);
v___x_569_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_569_, 0, v___x_407_);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
v___x_571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
return v___x_571_;
}
}
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_572_ = lean_unsigned_to_nat(2u);
v___x_573_ = l_Lean_Syntax_getArg(v___x_397_, v___x_572_);
lean_dec(v___x_397_);
lean_inc(v___x_573_);
v___x_574_ = l_Lean_Syntax_matchesNull(v___x_573_, v___x_396_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_575_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_573_);
v___x_576_ = l_Lean_Syntax_matchesNull(v___x_573_, v___x_575_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
lean_dec(v___x_573_);
v___x_577_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_578_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_577_);
lean_ctor_set(v___x_579_, 1, v___x_578_);
v___x_580_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_579_);
lean_ctor_set(v___x_581_, 1, v___x_580_);
v___x_582_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_581_, v_a_385_, v_a_386_);
return v___x_582_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_583_ = l_Lean_Syntax_getArg(v___x_573_, v___x_396_);
lean_dec(v___x_573_);
v___x_584_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_585_ = l_Lean_Syntax_isOfKind(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_586_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_587_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_588_, 0, v___x_586_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
v___x_589_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v___x_589_);
v___x_591_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_590_, v_a_385_, v_a_386_);
return v___x_591_;
}
else
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
lean_dec(v_stx_384_);
v___x_592_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_592_, 0, v___x_389_);
v___x_593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
v___x_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_594_, 0, v___x_593_);
return v___x_594_;
}
}
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec(v___x_573_);
lean_dec(v_stx_384_);
v___x_595_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_595_, 0, v___x_405_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
v___x_597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_597_, 0, v___x_596_);
return v___x_597_;
}
}
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = l_Lean_Syntax_getArg(v___x_397_, v___x_598_);
lean_dec(v___x_397_);
lean_inc(v___x_599_);
v___x_600_ = l_Lean_Syntax_matchesNull(v___x_599_, v___x_396_);
if (v___x_600_ == 0)
{
uint8_t v___x_601_; 
lean_inc(v___x_599_);
v___x_601_ = l_Lean_Syntax_matchesNull(v___x_599_, v___x_598_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec(v___x_599_);
v___x_602_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_603_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_602_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
v___x_605_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_604_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
v___x_607_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_606_, v_a_385_, v_a_386_);
return v___x_607_;
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; uint8_t v___x_610_; 
v___x_608_ = l_Lean_Syntax_getArg(v___x_599_, v___x_396_);
lean_dec(v___x_599_);
v___x_609_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_610_ = l_Lean_Syntax_isOfKind(v___x_608_, v___x_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_611_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_612_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_615_, v_a_385_, v_a_386_);
return v___x_616_;
}
else
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec(v_stx_384_);
v___x_617_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_617_, 0, v___x_389_);
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v___x_617_);
v___x_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
return v___x_619_;
}
}
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v___x_599_);
lean_dec(v_stx_384_);
v___x_620_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_620_, 0, v___x_403_);
v___x_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_621_, 0, v___x_620_);
v___x_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
return v___x_622_;
}
}
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; 
lean_dec(v___x_397_);
lean_dec(v_stx_384_);
v___x_623_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__59));
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
return v___x_624_;
}
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = lean_unsigned_to_nat(1u);
v___x_626_ = l_Lean_Syntax_getArg(v___x_397_, v___x_625_);
lean_dec(v___x_397_);
lean_inc(v___x_626_);
v___x_627_ = l_Lean_Syntax_matchesNull(v___x_626_, v___x_396_);
if (v___x_627_ == 0)
{
uint8_t v___x_628_; 
lean_inc(v___x_626_);
v___x_628_ = l_Lean_Syntax_matchesNull(v___x_626_, v___x_625_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
lean_dec(v___x_626_);
v___x_629_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_630_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_629_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set(v___x_633_, 1, v___x_632_);
v___x_634_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_633_, v_a_385_, v_a_386_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_635_ = l_Lean_Syntax_getArg(v___x_626_, v___x_396_);
lean_dec(v___x_626_);
v___x_636_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_637_ = l_Lean_Syntax_isOfKind(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_638_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_639_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_642_, v_a_385_, v_a_386_);
return v___x_643_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
lean_dec(v_stx_384_);
v___x_644_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_644_, 0, v___x_389_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
v___x_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
}
}
else
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v___x_626_);
lean_dec(v_stx_384_);
v___x_647_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_647_, 0, v___x_399_);
v___x_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_650_ = lean_unsigned_to_nat(1u);
v___x_651_ = l_Lean_Syntax_getArg(v___x_397_, v___x_650_);
lean_dec(v___x_397_);
lean_inc(v___x_651_);
v___x_652_ = l_Lean_Syntax_matchesNull(v___x_651_, v___x_396_);
if (v___x_652_ == 0)
{
uint8_t v___x_653_; 
lean_inc(v___x_651_);
v___x_653_ = l_Lean_Syntax_matchesNull(v___x_651_, v___x_650_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
lean_dec(v___x_651_);
v___x_654_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_655_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_656_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v___x_659_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_658_, v_a_385_, v_a_386_);
return v___x_659_;
}
else
{
lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_660_ = l_Lean_Syntax_getArg(v___x_651_, v___x_396_);
lean_dec(v___x_651_);
v___x_661_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_662_ = l_Lean_Syntax_isOfKind(v___x_660_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_663_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_664_ = l_Lean_MessageData_ofSyntax(v_stx_384_);
v___x_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_663_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
v___x_666_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_667_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_665_);
lean_ctor_set(v___x_667_, 1, v___x_666_);
v___x_668_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_667_, v_a_385_, v_a_386_);
return v___x_668_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
lean_dec(v_stx_384_);
v___x_669_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_669_, 0, v___x_389_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; 
lean_dec(v___x_651_);
lean_dec(v_stx_384_);
v___x_672_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__61));
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object* v_stx_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_674_, v_a_675_, v_a_676_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object* v_00_u03b1_679_, lean_object* v_msg_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_680_, v___y_681_, v___y_682_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object* v_00_u03b1_685_, lean_object* v_msg_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(v_00_u03b1_685_, v_msg_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object* v_00_u03b1_691_, lean_object* v_ref_692_, lean_object* v_msg_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_692_, v_msg_693_, v___y_694_, v___y_695_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object* v_00_u03b1_698_, lean_object* v_ref_699_, lean_object* v_msg_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(v_00_u03b1_698_, v_ref_699_, v_msg_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v_ref_699_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object* v_stx_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_709_ = lean_unsigned_to_nat(1u);
v___x_710_ = l_Lean_Syntax_getArg(v_stx_705_, v___x_709_);
v___x_711_ = l_Lean_Syntax_isNone(v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = lean_unsigned_to_nat(0u);
v___x_713_ = l_Lean_Syntax_getArg(v___x_710_, v___x_712_);
lean_dec(v___x_710_);
v___x_714_ = l_Lean_Meta_Grind_getAttrKindCore(v___x_713_, v_a_706_, v_a_707_);
return v___x_714_;
}
else
{
lean_object* v___x_715_; lean_object* v___x_716_; 
lean_dec(v___x_710_);
v___x_715_ = lean_box(3);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
return v___x_716_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object* v_stx_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_717_, v_a_718_, v_a_719_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_stx_717_);
return v_res_721_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1(void){
_start:
{
lean_object* v___x_723_; lean_object* v___x_724_; 
v___x_723_ = ((lean_object*)(l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0));
v___x_724_ = l_Lean_stringToMessageData(v___x_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_728_ = lean_obj_once(&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1, &l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1);
v___x_729_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_728_, v_a_725_, v_a_726_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_730_, v_a_731_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object* v_00_u03b1_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_735_, v_a_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object* v_00_u03b1_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(v_00_u03b1_739_, v_a_740_, v_a_741_);
lean_dec(v_a_741_);
lean_dec_ref(v_a_740_);
return v_res_743_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_744_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_745_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_747_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object* v_ext_749_, lean_object* v_b_750_, uint8_t v_kind_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_currNamespace_755_; lean_object* v___x_756_; lean_object* v_env_757_; lean_object* v_nextMacroScope_758_; lean_object* v_ngen_759_; lean_object* v_auxDeclNGen_760_; lean_object* v_traceState_761_; lean_object* v_messages_762_; lean_object* v_infoState_763_; lean_object* v_snapshotTasks_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_776_; 
v_currNamespace_755_ = lean_ctor_get(v___y_752_, 6);
v___x_756_ = lean_st_ref_take(v___y_753_);
v_env_757_ = lean_ctor_get(v___x_756_, 0);
v_nextMacroScope_758_ = lean_ctor_get(v___x_756_, 1);
v_ngen_759_ = lean_ctor_get(v___x_756_, 2);
v_auxDeclNGen_760_ = lean_ctor_get(v___x_756_, 3);
v_traceState_761_ = lean_ctor_get(v___x_756_, 4);
v_messages_762_ = lean_ctor_get(v___x_756_, 6);
v_infoState_763_ = lean_ctor_get(v___x_756_, 7);
v_snapshotTasks_764_ = lean_ctor_get(v___x_756_, 8);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v___x_756_, 5);
lean_dec(v_unused_777_);
v___x_766_ = v___x_756_;
v_isShared_767_ = v_isSharedCheck_776_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_snapshotTasks_764_);
lean_inc(v_infoState_763_);
lean_inc(v_messages_762_);
lean_inc(v_traceState_761_);
lean_inc(v_auxDeclNGen_760_);
lean_inc(v_ngen_759_);
lean_inc(v_nextMacroScope_758_);
lean_inc(v_env_757_);
lean_dec(v___x_756_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_776_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
lean_inc(v_currNamespace_755_);
v___x_768_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_757_, v_ext_749_, v_b_750_, v_kind_751_, v_currNamespace_755_);
v___x_769_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 5, v___x_769_);
lean_ctor_set(v___x_766_, 0, v___x_768_);
v___x_771_ = v___x_766_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_nextMacroScope_758_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v_ngen_759_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_auxDeclNGen_760_);
lean_ctor_set(v_reuseFailAlloc_775_, 4, v_traceState_761_);
lean_ctor_set(v_reuseFailAlloc_775_, 5, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_775_, 6, v_messages_762_);
lean_ctor_set(v_reuseFailAlloc_775_, 7, v_infoState_763_);
lean_ctor_set(v_reuseFailAlloc_775_, 8, v_snapshotTasks_764_);
v___x_771_ = v_reuseFailAlloc_775_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_772_ = lean_st_ref_set(v___y_753_, v___x_771_);
v___x_773_ = lean_box(0);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_778_, lean_object* v_b_779_, lean_object* v_kind_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
uint8_t v_kind_boxed_784_; lean_object* v_res_785_; 
v_kind_boxed_784_ = lean_unbox(v_kind_780_);
v_res_785_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_778_, v_b_779_, v_kind_boxed_784_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_786_, lean_object* v_00_u03b2_787_, lean_object* v_00_u03c3_788_, lean_object* v_ext_789_, lean_object* v_b_790_, uint8_t v_kind_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_789_, v_b_790_, v_kind_791_, v___y_792_, v___y_793_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_796_, lean_object* v_00_u03b2_797_, lean_object* v_00_u03c3_798_, lean_object* v_ext_799_, lean_object* v_b_800_, lean_object* v_kind_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
uint8_t v_kind_boxed_805_; lean_object* v_res_806_; 
v_kind_boxed_805_ = lean_unbox(v_kind_801_);
v_res_806_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_796_, v_00_u03b2_797_, v_00_u03c3_798_, v_ext_799_, v_b_800_, v_kind_boxed_805_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_807_, lean_object* v_declName_808_, uint8_t v_eager_809_, uint8_t v_attrKind_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v___x_814_; 
lean_inc(v_declName_808_);
v___x_814_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_808_, v_eager_809_, v_a_811_, v_a_812_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; 
lean_dec_ref(v___x_814_);
v___x_815_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_815_, 0, v_declName_808_);
lean_ctor_set_uint8(v___x_815_, sizeof(void*)*1, v_eager_809_);
v___x_816_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_807_, v___x_815_, v_attrKind_810_, v_a_811_, v_a_812_);
return v___x_816_;
}
else
{
lean_dec(v_declName_808_);
lean_dec_ref(v_ext_807_);
return v___x_814_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_817_, lean_object* v_declName_818_, lean_object* v_eager_819_, lean_object* v_attrKind_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
uint8_t v_eager_boxed_824_; uint8_t v_attrKind_boxed_825_; lean_object* v_res_826_; 
v_eager_boxed_824_ = lean_unbox(v_eager_819_);
v_attrKind_boxed_825_ = lean_unbox(v_attrKind_820_);
v_res_826_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_817_, v_declName_818_, v_eager_boxed_824_, v_attrKind_boxed_825_, v_a_821_, v_a_822_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_827_, lean_object* v_declName_828_, uint8_t v_attrKind_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___x_833_; 
lean_inc(v_declName_828_);
v___x_833_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_828_, v_a_830_, v_a_831_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_841_; 
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_841_ == 0)
{
lean_object* v_unused_842_; 
v_unused_842_ = lean_ctor_get(v___x_833_, 0);
lean_dec(v_unused_842_);
v___x_835_ = v___x_833_;
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
else
{
lean_dec(v___x_833_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
lean_ctor_set(v___x_835_, 0, v_declName_828_);
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_declName_828_);
v___x_838_ = v_reuseFailAlloc_840_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; 
v___x_839_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_827_, v___x_838_, v_attrKind_829_, v_a_830_, v_a_831_);
return v___x_839_;
}
}
}
else
{
lean_dec(v_declName_828_);
lean_dec_ref(v_ext_827_);
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_843_, lean_object* v_declName_844_, lean_object* v_attrKind_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
uint8_t v_attrKind_boxed_849_; lean_object* v_res_850_; 
v_attrKind_boxed_849_ = lean_unbox(v_attrKind_845_);
v_res_850_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_843_, v_declName_844_, v_attrKind_boxed_849_, v_a_846_, v_a_847_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_851_, lean_object* v_declName_852_, uint8_t v_attrKind_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_857_, 0, v_declName_852_);
v___x_858_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_851_, v___x_857_, v_attrKind_853_, v_a_854_, v_a_855_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_859_, lean_object* v_declName_860_, lean_object* v_attrKind_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
uint8_t v_attrKind_boxed_865_; lean_object* v_res_866_; 
v_attrKind_boxed_865_ = lean_unbox(v_attrKind_861_);
v_res_866_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_859_, v_declName_860_, v_attrKind_boxed_865_, v_a_862_, v_a_863_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_867_, lean_object* v_s_868_){
_start:
{
lean_object* v_casesTypes_869_; lean_object* v_funCC_870_; lean_object* v_ematch_871_; lean_object* v_inj_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
v_casesTypes_869_ = lean_ctor_get(v_s_868_, 0);
v_funCC_870_ = lean_ctor_get(v_s_868_, 2);
v_ematch_871_ = lean_ctor_get(v_s_868_, 3);
v_inj_872_ = lean_ctor_get(v_s_868_, 4);
v_isSharedCheck_879_ = !lean_is_exclusive(v_s_868_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; 
v_unused_880_ = lean_ctor_get(v_s_868_, 1);
lean_dec(v_unused_880_);
v___x_874_ = v_s_868_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_inj_872_);
lean_inc(v_ematch_871_);
lean_inc(v_funCC_870_);
lean_inc(v_casesTypes_869_);
lean_dec(v_s_868_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 1, v_a_867_);
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_casesTypes_869_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_a_867_);
lean_ctor_set(v_reuseFailAlloc_878_, 2, v_funCC_870_);
lean_ctor_set(v_reuseFailAlloc_878_, 3, v_ematch_871_);
lean_ctor_set(v_reuseFailAlloc_878_, 4, v_inj_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_881_, lean_object* v_declName_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_886_; lean_object* v_ext_887_; lean_object* v_toEnvExtension_888_; lean_object* v_env_889_; lean_object* v_asyncMode_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v_extThms_893_; lean_object* v___x_894_; 
v___x_886_ = lean_st_ref_get(v_a_884_);
v_ext_887_ = lean_ctor_get(v_ext_881_, 1);
v_toEnvExtension_888_ = lean_ctor_get(v_ext_887_, 0);
v_env_889_ = lean_ctor_get(v___x_886_, 0);
lean_inc_ref(v_env_889_);
lean_dec(v___x_886_);
v_asyncMode_890_ = lean_ctor_get(v_toEnvExtension_888_, 2);
v___x_891_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_892_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_891_, v_ext_881_, v_env_889_, v_asyncMode_890_);
v_extThms_893_ = lean_ctor_get(v___x_892_, 1);
lean_inc_ref(v_extThms_893_);
lean_dec(v___x_892_);
v___x_894_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_893_, v_declName_882_, v_a_883_, v_a_884_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_924_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_924_ == 0)
{
v___x_897_ = v___x_894_;
v_isShared_898_ = v_isSharedCheck_924_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_894_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_924_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v_env_900_; lean_object* v_nextMacroScope_901_; lean_object* v_ngen_902_; lean_object* v_auxDeclNGen_903_; lean_object* v_traceState_904_; lean_object* v_messages_905_; lean_object* v_infoState_906_; lean_object* v_snapshotTasks_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_922_; 
v___x_899_ = lean_st_ref_take(v_a_884_);
v_env_900_ = lean_ctor_get(v___x_899_, 0);
v_nextMacroScope_901_ = lean_ctor_get(v___x_899_, 1);
v_ngen_902_ = lean_ctor_get(v___x_899_, 2);
v_auxDeclNGen_903_ = lean_ctor_get(v___x_899_, 3);
v_traceState_904_ = lean_ctor_get(v___x_899_, 4);
v_messages_905_ = lean_ctor_get(v___x_899_, 6);
v_infoState_906_ = lean_ctor_get(v___x_899_, 7);
v_snapshotTasks_907_ = lean_ctor_get(v___x_899_, 8);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_922_ == 0)
{
lean_object* v_unused_923_; 
v_unused_923_ = lean_ctor_get(v___x_899_, 5);
lean_dec(v_unused_923_);
v___x_909_ = v___x_899_;
v_isShared_910_ = v_isSharedCheck_922_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_snapshotTasks_907_);
lean_inc(v_infoState_906_);
lean_inc(v_messages_905_);
lean_inc(v_traceState_904_);
lean_inc(v_auxDeclNGen_903_);
lean_inc(v_ngen_902_);
lean_inc(v_nextMacroScope_901_);
lean_inc(v_env_900_);
lean_dec(v___x_899_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_922_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___f_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_915_; 
v___f_911_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_911_, 0, v_a_895_);
v___x_912_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_881_, v_env_900_, v___f_911_);
v___x_913_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_910_ == 0)
{
lean_ctor_set(v___x_909_, 5, v___x_913_);
lean_ctor_set(v___x_909_, 0, v___x_912_);
v___x_915_ = v___x_909_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_912_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_nextMacroScope_901_);
lean_ctor_set(v_reuseFailAlloc_921_, 2, v_ngen_902_);
lean_ctor_set(v_reuseFailAlloc_921_, 3, v_auxDeclNGen_903_);
lean_ctor_set(v_reuseFailAlloc_921_, 4, v_traceState_904_);
lean_ctor_set(v_reuseFailAlloc_921_, 5, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_921_, 6, v_messages_905_);
lean_ctor_set(v_reuseFailAlloc_921_, 7, v_infoState_906_);
lean_ctor_set(v_reuseFailAlloc_921_, 8, v_snapshotTasks_907_);
v___x_915_ = v_reuseFailAlloc_921_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_916_ = lean_st_ref_set(v_a_884_, v___x_915_);
v___x_917_ = lean_box(0);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_917_);
v___x_919_ = v___x_897_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v_ext_881_);
v_a_925_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_894_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_894_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_933_, lean_object* v_declName_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_933_, v_declName_934_, v_a_935_, v_a_936_);
lean_dec(v_a_936_);
lean_dec_ref(v_a_935_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_939_, lean_object* v_s_940_){
_start:
{
lean_object* v_extThms_941_; lean_object* v_funCC_942_; lean_object* v_ematch_943_; lean_object* v_inj_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v_extThms_941_ = lean_ctor_get(v_s_940_, 1);
v_funCC_942_ = lean_ctor_get(v_s_940_, 2);
v_ematch_943_ = lean_ctor_get(v_s_940_, 3);
v_inj_944_ = lean_ctor_get(v_s_940_, 4);
v_isSharedCheck_951_ = !lean_is_exclusive(v_s_940_);
if (v_isSharedCheck_951_ == 0)
{
lean_object* v_unused_952_; 
v_unused_952_ = lean_ctor_get(v_s_940_, 0);
lean_dec(v_unused_952_);
v___x_946_ = v_s_940_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_inj_944_);
lean_inc(v_ematch_943_);
lean_inc(v_funCC_942_);
lean_inc(v_extThms_941_);
lean_dec(v_s_940_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 0, v_a_939_);
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_939_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_extThms_941_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_funCC_942_);
lean_ctor_set(v_reuseFailAlloc_950_, 3, v_ematch_943_);
lean_ctor_set(v_reuseFailAlloc_950_, 4, v_inj_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_953_, lean_object* v_declName_954_, lean_object* v_a_955_, lean_object* v_a_956_){
_start:
{
lean_object* v___x_958_; 
lean_inc(v_declName_954_);
v___x_958_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v___x_959_; lean_object* v_ext_960_; lean_object* v_toEnvExtension_961_; lean_object* v_env_962_; lean_object* v_asyncMode_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_casesTypes_966_; lean_object* v___x_967_; 
lean_dec_ref(v___x_958_);
v___x_959_ = lean_st_ref_get(v_a_956_);
v_ext_960_ = lean_ctor_get(v_ext_953_, 1);
v_toEnvExtension_961_ = lean_ctor_get(v_ext_960_, 0);
v_env_962_ = lean_ctor_get(v___x_959_, 0);
lean_inc_ref(v_env_962_);
lean_dec(v___x_959_);
v_asyncMode_963_ = lean_ctor_get(v_toEnvExtension_961_, 2);
v___x_964_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_965_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_964_, v_ext_953_, v_env_962_, v_asyncMode_963_);
v_casesTypes_966_ = lean_ctor_get(v___x_965_, 0);
lean_inc_ref(v_casesTypes_966_);
lean_dec(v___x_965_);
v___x_967_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_966_, v_declName_954_, v_a_955_, v_a_956_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_a_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_997_; 
v_a_968_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_997_ == 0)
{
v___x_970_ = v___x_967_;
v_isShared_971_ = v_isSharedCheck_997_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_997_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v___x_972_; lean_object* v_env_973_; lean_object* v_nextMacroScope_974_; lean_object* v_ngen_975_; lean_object* v_auxDeclNGen_976_; lean_object* v_traceState_977_; lean_object* v_messages_978_; lean_object* v_infoState_979_; lean_object* v_snapshotTasks_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_995_; 
v___x_972_ = lean_st_ref_take(v_a_956_);
v_env_973_ = lean_ctor_get(v___x_972_, 0);
v_nextMacroScope_974_ = lean_ctor_get(v___x_972_, 1);
v_ngen_975_ = lean_ctor_get(v___x_972_, 2);
v_auxDeclNGen_976_ = lean_ctor_get(v___x_972_, 3);
v_traceState_977_ = lean_ctor_get(v___x_972_, 4);
v_messages_978_ = lean_ctor_get(v___x_972_, 6);
v_infoState_979_ = lean_ctor_get(v___x_972_, 7);
v_snapshotTasks_980_ = lean_ctor_get(v___x_972_, 8);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_995_ == 0)
{
lean_object* v_unused_996_; 
v_unused_996_ = lean_ctor_get(v___x_972_, 5);
lean_dec(v_unused_996_);
v___x_982_ = v___x_972_;
v_isShared_983_ = v_isSharedCheck_995_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_snapshotTasks_980_);
lean_inc(v_infoState_979_);
lean_inc(v_messages_978_);
lean_inc(v_traceState_977_);
lean_inc(v_auxDeclNGen_976_);
lean_inc(v_ngen_975_);
lean_inc(v_nextMacroScope_974_);
lean_inc(v_env_973_);
lean_dec(v___x_972_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_995_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___f_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___f_984_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_984_, 0, v_a_968_);
v___x_985_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_953_, v_env_973_, v___f_984_);
v___x_986_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 5, v___x_986_);
lean_ctor_set(v___x_982_, 0, v___x_985_);
v___x_988_ = v___x_982_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_985_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_nextMacroScope_974_);
lean_ctor_set(v_reuseFailAlloc_994_, 2, v_ngen_975_);
lean_ctor_set(v_reuseFailAlloc_994_, 3, v_auxDeclNGen_976_);
lean_ctor_set(v_reuseFailAlloc_994_, 4, v_traceState_977_);
lean_ctor_set(v_reuseFailAlloc_994_, 5, v___x_986_);
lean_ctor_set(v_reuseFailAlloc_994_, 6, v_messages_978_);
lean_ctor_set(v_reuseFailAlloc_994_, 7, v_infoState_979_);
lean_ctor_set(v_reuseFailAlloc_994_, 8, v_snapshotTasks_980_);
v___x_988_ = v_reuseFailAlloc_994_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_989_ = lean_st_ref_set(v_a_956_, v___x_988_);
v___x_990_ = lean_box(0);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v___x_990_);
v___x_992_ = v___x_970_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_990_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec_ref(v_ext_953_);
v_a_998_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_967_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_967_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
else
{
lean_dec(v_declName_954_);
lean_dec_ref(v_ext_953_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_1006_, lean_object* v_declName_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_1006_, v_declName_1007_, v_a_1008_, v_a_1009_);
lean_dec(v_a_1009_);
lean_dec_ref(v_a_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_1012_, lean_object* v_s_1013_){
_start:
{
lean_object* v_casesTypes_1014_; lean_object* v_extThms_1015_; lean_object* v_ematch_1016_; lean_object* v_inj_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_casesTypes_1014_ = lean_ctor_get(v_s_1013_, 0);
v_extThms_1015_ = lean_ctor_get(v_s_1013_, 1);
v_ematch_1016_ = lean_ctor_get(v_s_1013_, 3);
v_inj_1017_ = lean_ctor_get(v_s_1013_, 4);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_s_1013_);
if (v_isSharedCheck_1024_ == 0)
{
lean_object* v_unused_1025_; 
v_unused_1025_ = lean_ctor_get(v_s_1013_, 2);
lean_dec(v_unused_1025_);
v___x_1019_ = v_s_1013_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_inj_1017_);
lean_inc(v_ematch_1016_);
lean_inc(v_extThms_1015_);
lean_inc(v_casesTypes_1014_);
lean_dec(v_s_1013_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 2, v___x_1012_);
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_casesTypes_1014_);
lean_ctor_set(v_reuseFailAlloc_1023_, 1, v_extThms_1015_);
lean_ctor_set(v_reuseFailAlloc_1023_, 2, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1023_, 3, v_ematch_1016_);
lean_ctor_set(v_reuseFailAlloc_1023_, 4, v_inj_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_1026_, lean_object* v_t_1027_){
_start:
{
if (lean_obj_tag(v_t_1027_) == 0)
{
lean_object* v_k_1028_; lean_object* v_v_1029_; lean_object* v_l_1030_; lean_object* v_r_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1685_; 
v_k_1028_ = lean_ctor_get(v_t_1027_, 1);
v_v_1029_ = lean_ctor_get(v_t_1027_, 2);
v_l_1030_ = lean_ctor_get(v_t_1027_, 3);
v_r_1031_ = lean_ctor_get(v_t_1027_, 4);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_t_1027_);
if (v_isSharedCheck_1685_ == 0)
{
lean_object* v_unused_1686_; 
v_unused_1686_ = lean_ctor_get(v_t_1027_, 0);
lean_dec(v_unused_1686_);
v___x_1033_ = v_t_1027_;
v_isShared_1034_ = v_isSharedCheck_1685_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_r_1031_);
lean_inc(v_l_1030_);
lean_inc(v_v_1029_);
lean_inc(v_k_1028_);
lean_dec(v_t_1027_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1685_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
uint8_t v___x_1035_; 
v___x_1035_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1026_, v_k_1028_);
switch(v___x_1035_)
{
case 0:
{
lean_object* v_impl_1036_; lean_object* v___x_1037_; 
v_impl_1036_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1026_, v_l_1030_);
v___x_1037_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1036_) == 0)
{
if (lean_obj_tag(v_r_1031_) == 0)
{
lean_object* v_size_1038_; lean_object* v_size_1039_; lean_object* v_k_1040_; lean_object* v_v_1041_; lean_object* v_l_1042_; lean_object* v_r_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_size_1038_ = lean_ctor_get(v_impl_1036_, 0);
lean_inc(v_size_1038_);
v_size_1039_ = lean_ctor_get(v_r_1031_, 0);
v_k_1040_ = lean_ctor_get(v_r_1031_, 1);
v_v_1041_ = lean_ctor_get(v_r_1031_, 2);
v_l_1042_ = lean_ctor_get(v_r_1031_, 3);
lean_inc(v_l_1042_);
v_r_1043_ = lean_ctor_get(v_r_1031_, 4);
v___x_1044_ = lean_unsigned_to_nat(3u);
v___x_1045_ = lean_nat_mul(v___x_1044_, v_size_1038_);
v___x_1046_ = lean_nat_dec_lt(v___x_1045_, v_size_1039_);
lean_dec(v___x_1045_);
if (v___x_1046_ == 0)
{
lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1050_; 
lean_dec(v_l_1042_);
v___x_1047_ = lean_nat_add(v___x_1037_, v_size_1038_);
lean_dec(v_size_1038_);
v___x_1048_ = lean_nat_add(v___x_1047_, v_size_1039_);
lean_dec(v___x_1047_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 3, v_impl_1036_);
lean_ctor_set(v___x_1033_, 0, v___x_1048_);
v___x_1050_ = v___x_1033_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v___x_1048_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1051_, 3, v_impl_1036_);
lean_ctor_set(v_reuseFailAlloc_1051_, 4, v_r_1031_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
else
{
lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1115_; 
lean_inc(v_r_1043_);
lean_inc(v_v_1041_);
lean_inc(v_k_1040_);
lean_inc(v_size_1039_);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_r_1031_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; lean_object* v_unused_1117_; lean_object* v_unused_1118_; lean_object* v_unused_1119_; lean_object* v_unused_1120_; 
v_unused_1116_ = lean_ctor_get(v_r_1031_, 4);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v_r_1031_, 3);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_r_1031_, 2);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_r_1031_, 1);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_r_1031_, 0);
lean_dec(v_unused_1120_);
v___x_1053_ = v_r_1031_;
v_isShared_1054_ = v_isSharedCheck_1115_;
goto v_resetjp_1052_;
}
else
{
lean_dec(v_r_1031_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1115_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v_size_1055_; lean_object* v_k_1056_; lean_object* v_v_1057_; lean_object* v_l_1058_; lean_object* v_r_1059_; lean_object* v_size_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v_size_1055_ = lean_ctor_get(v_l_1042_, 0);
v_k_1056_ = lean_ctor_get(v_l_1042_, 1);
v_v_1057_ = lean_ctor_get(v_l_1042_, 2);
v_l_1058_ = lean_ctor_get(v_l_1042_, 3);
v_r_1059_ = lean_ctor_get(v_l_1042_, 4);
v_size_1060_ = lean_ctor_get(v_r_1043_, 0);
v___x_1061_ = lean_unsigned_to_nat(2u);
v___x_1062_ = lean_nat_mul(v___x_1061_, v_size_1060_);
v___x_1063_ = lean_nat_dec_lt(v_size_1055_, v___x_1062_);
lean_dec(v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1091_; 
lean_inc(v_r_1059_);
lean_inc(v_l_1058_);
lean_inc(v_v_1057_);
lean_inc(v_k_1056_);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_l_1042_);
if (v_isSharedCheck_1091_ == 0)
{
lean_object* v_unused_1092_; lean_object* v_unused_1093_; lean_object* v_unused_1094_; lean_object* v_unused_1095_; lean_object* v_unused_1096_; 
v_unused_1092_ = lean_ctor_get(v_l_1042_, 4);
lean_dec(v_unused_1092_);
v_unused_1093_ = lean_ctor_get(v_l_1042_, 3);
lean_dec(v_unused_1093_);
v_unused_1094_ = lean_ctor_get(v_l_1042_, 2);
lean_dec(v_unused_1094_);
v_unused_1095_ = lean_ctor_get(v_l_1042_, 1);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_l_1042_, 0);
lean_dec(v_unused_1096_);
v___x_1065_ = v_l_1042_;
v_isShared_1066_ = v_isSharedCheck_1091_;
goto v_resetjp_1064_;
}
else
{
lean_dec(v_l_1042_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1091_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; lean_object* v___y_1081_; 
v___x_1067_ = lean_nat_add(v___x_1037_, v_size_1038_);
lean_dec(v_size_1038_);
v___x_1068_ = lean_nat_add(v___x_1067_, v_size_1039_);
lean_dec(v_size_1039_);
if (lean_obj_tag(v_l_1058_) == 0)
{
lean_object* v_size_1089_; 
v_size_1089_ = lean_ctor_get(v_l_1058_, 0);
lean_inc(v_size_1089_);
v___y_1081_ = v_size_1089_;
goto v___jp_1080_;
}
else
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_unsigned_to_nat(0u);
v___y_1081_ = v___x_1090_;
goto v___jp_1080_;
}
v___jp_1069_:
{
lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___x_1073_ = lean_nat_add(v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec(v___y_1071_);
if (v_isShared_1066_ == 0)
{
lean_ctor_set(v___x_1065_, 4, v_r_1043_);
lean_ctor_set(v___x_1065_, 3, v_r_1059_);
lean_ctor_set(v___x_1065_, 2, v_v_1041_);
lean_ctor_set(v___x_1065_, 1, v_k_1040_);
lean_ctor_set(v___x_1065_, 0, v___x_1073_);
v___x_1075_ = v___x_1065_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_k_1040_);
lean_ctor_set(v_reuseFailAlloc_1079_, 2, v_v_1041_);
lean_ctor_set(v_reuseFailAlloc_1079_, 3, v_r_1059_);
lean_ctor_set(v_reuseFailAlloc_1079_, 4, v_r_1043_);
v___x_1075_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1077_; 
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 4, v___x_1075_);
lean_ctor_set(v___x_1053_, 3, v___y_1070_);
lean_ctor_set(v___x_1053_, 2, v_v_1057_);
lean_ctor_set(v___x_1053_, 1, v_k_1056_);
lean_ctor_set(v___x_1053_, 0, v___x_1068_);
v___x_1077_ = v___x_1053_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_k_1056_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_v_1057_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v___y_1070_);
lean_ctor_set(v_reuseFailAlloc_1078_, 4, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
v___jp_1080_:
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = lean_nat_add(v___x_1067_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec(v___x_1067_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v_l_1058_);
lean_ctor_set(v___x_1033_, 3, v_impl_1036_);
lean_ctor_set(v___x_1033_, 0, v___x_1082_);
v___x_1084_ = v___x_1033_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1088_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1088_, 3, v_impl_1036_);
lean_ctor_set(v_reuseFailAlloc_1088_, 4, v_l_1058_);
v___x_1084_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_nat_add(v___x_1037_, v_size_1060_);
if (lean_obj_tag(v_r_1059_) == 0)
{
lean_object* v_size_1086_; 
v_size_1086_ = lean_ctor_get(v_r_1059_, 0);
lean_inc(v_size_1086_);
v___y_1070_ = v___x_1084_;
v___y_1071_ = v___x_1085_;
v___y_1072_ = v_size_1086_;
goto v___jp_1069_;
}
else
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_unsigned_to_nat(0u);
v___y_1070_ = v___x_1084_;
v___y_1071_ = v___x_1085_;
v___y_1072_ = v___x_1087_;
goto v___jp_1069_;
}
}
}
}
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1101_; 
lean_del_object(v___x_1033_);
v___x_1097_ = lean_nat_add(v___x_1037_, v_size_1038_);
lean_dec(v_size_1038_);
v___x_1098_ = lean_nat_add(v___x_1097_, v_size_1039_);
lean_dec(v_size_1039_);
v___x_1099_ = lean_nat_add(v___x_1097_, v_size_1055_);
lean_dec(v___x_1097_);
lean_inc_ref(v_impl_1036_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 4, v_l_1042_);
lean_ctor_set(v___x_1053_, 3, v_impl_1036_);
lean_ctor_set(v___x_1053_, 2, v_v_1029_);
lean_ctor_set(v___x_1053_, 1, v_k_1028_);
lean_ctor_set(v___x_1053_, 0, v___x_1099_);
v___x_1101_ = v___x_1053_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1099_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_impl_1036_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_l_1042_);
v___x_1101_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
v_isSharedCheck_1108_ = !lean_is_exclusive(v_impl_1036_);
if (v_isSharedCheck_1108_ == 0)
{
lean_object* v_unused_1109_; lean_object* v_unused_1110_; lean_object* v_unused_1111_; lean_object* v_unused_1112_; lean_object* v_unused_1113_; 
v_unused_1109_ = lean_ctor_get(v_impl_1036_, 4);
lean_dec(v_unused_1109_);
v_unused_1110_ = lean_ctor_get(v_impl_1036_, 3);
lean_dec(v_unused_1110_);
v_unused_1111_ = lean_ctor_get(v_impl_1036_, 2);
lean_dec(v_unused_1111_);
v_unused_1112_ = lean_ctor_get(v_impl_1036_, 1);
lean_dec(v_unused_1112_);
v_unused_1113_ = lean_ctor_get(v_impl_1036_, 0);
lean_dec(v_unused_1113_);
v___x_1103_ = v_impl_1036_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_dec(v_impl_1036_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
lean_ctor_set(v___x_1103_, 4, v_r_1043_);
lean_ctor_set(v___x_1103_, 3, v___x_1101_);
lean_ctor_set(v___x_1103_, 2, v_v_1041_);
lean_ctor_set(v___x_1103_, 1, v_k_1040_);
lean_ctor_set(v___x_1103_, 0, v___x_1098_);
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_k_1040_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_v_1041_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1107_, 4, v_r_1043_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1121_; lean_object* v___x_1122_; lean_object* v___x_1124_; 
v_size_1121_ = lean_ctor_get(v_impl_1036_, 0);
lean_inc(v_size_1121_);
v___x_1122_ = lean_nat_add(v___x_1037_, v_size_1121_);
lean_dec(v_size_1121_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 3, v_impl_1036_);
lean_ctor_set(v___x_1033_, 0, v___x_1122_);
v___x_1124_ = v___x_1033_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1125_, 3, v_impl_1036_);
lean_ctor_set(v_reuseFailAlloc_1125_, 4, v_r_1031_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
else
{
if (lean_obj_tag(v_r_1031_) == 0)
{
lean_object* v_l_1126_; 
v_l_1126_ = lean_ctor_get(v_r_1031_, 3);
lean_inc(v_l_1126_);
if (lean_obj_tag(v_l_1126_) == 0)
{
lean_object* v_r_1127_; 
v_r_1127_ = lean_ctor_get(v_r_1031_, 4);
lean_inc(v_r_1127_);
if (lean_obj_tag(v_r_1127_) == 0)
{
lean_object* v_size_1128_; lean_object* v_k_1129_; lean_object* v_v_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1143_; 
v_size_1128_ = lean_ctor_get(v_r_1031_, 0);
v_k_1129_ = lean_ctor_get(v_r_1031_, 1);
v_v_1130_ = lean_ctor_get(v_r_1031_, 2);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_r_1031_);
if (v_isSharedCheck_1143_ == 0)
{
lean_object* v_unused_1144_; lean_object* v_unused_1145_; 
v_unused_1144_ = lean_ctor_get(v_r_1031_, 4);
lean_dec(v_unused_1144_);
v_unused_1145_ = lean_ctor_get(v_r_1031_, 3);
lean_dec(v_unused_1145_);
v___x_1132_ = v_r_1031_;
v_isShared_1133_ = v_isSharedCheck_1143_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_v_1130_);
lean_inc(v_k_1129_);
lean_inc(v_size_1128_);
lean_dec(v_r_1031_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1143_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v_size_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v_size_1134_ = lean_ctor_get(v_l_1126_, 0);
v___x_1135_ = lean_nat_add(v___x_1037_, v_size_1128_);
lean_dec(v_size_1128_);
v___x_1136_ = lean_nat_add(v___x_1037_, v_size_1134_);
if (v_isShared_1133_ == 0)
{
lean_ctor_set(v___x_1132_, 4, v_l_1126_);
lean_ctor_set(v___x_1132_, 3, v_impl_1036_);
lean_ctor_set(v___x_1132_, 2, v_v_1029_);
lean_ctor_set(v___x_1132_, 1, v_k_1028_);
lean_ctor_set(v___x_1132_, 0, v___x_1136_);
v___x_1138_ = v___x_1132_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1142_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1142_, 3, v_impl_1036_);
lean_ctor_set(v_reuseFailAlloc_1142_, 4, v_l_1126_);
v___x_1138_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1140_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v_r_1127_);
lean_ctor_set(v___x_1033_, 3, v___x_1138_);
lean_ctor_set(v___x_1033_, 2, v_v_1130_);
lean_ctor_set(v___x_1033_, 1, v_k_1129_);
lean_ctor_set(v___x_1033_, 0, v___x_1135_);
v___x_1140_ = v___x_1033_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_k_1129_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_v_1130_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v_r_1127_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
else
{
lean_object* v_k_1146_; lean_object* v_v_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1170_; 
v_k_1146_ = lean_ctor_get(v_r_1031_, 1);
v_v_1147_ = lean_ctor_get(v_r_1031_, 2);
v_isSharedCheck_1170_ = !lean_is_exclusive(v_r_1031_);
if (v_isSharedCheck_1170_ == 0)
{
lean_object* v_unused_1171_; lean_object* v_unused_1172_; lean_object* v_unused_1173_; 
v_unused_1171_ = lean_ctor_get(v_r_1031_, 4);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_r_1031_, 3);
lean_dec(v_unused_1172_);
v_unused_1173_ = lean_ctor_get(v_r_1031_, 0);
lean_dec(v_unused_1173_);
v___x_1149_ = v_r_1031_;
v_isShared_1150_ = v_isSharedCheck_1170_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_v_1147_);
lean_inc(v_k_1146_);
lean_dec(v_r_1031_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1170_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v_k_1151_; lean_object* v_v_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1166_; 
v_k_1151_ = lean_ctor_get(v_l_1126_, 1);
v_v_1152_ = lean_ctor_get(v_l_1126_, 2);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_l_1126_);
if (v_isSharedCheck_1166_ == 0)
{
lean_object* v_unused_1167_; lean_object* v_unused_1168_; lean_object* v_unused_1169_; 
v_unused_1167_ = lean_ctor_get(v_l_1126_, 4);
lean_dec(v_unused_1167_);
v_unused_1168_ = lean_ctor_get(v_l_1126_, 3);
lean_dec(v_unused_1168_);
v_unused_1169_ = lean_ctor_get(v_l_1126_, 0);
lean_dec(v_unused_1169_);
v___x_1154_ = v_l_1126_;
v_isShared_1155_ = v_isSharedCheck_1166_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_v_1152_);
lean_inc(v_k_1151_);
lean_dec(v_l_1126_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1166_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1156_ = lean_unsigned_to_nat(3u);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 4, v_r_1127_);
lean_ctor_set(v___x_1154_, 3, v_r_1127_);
lean_ctor_set(v___x_1154_, 2, v_v_1029_);
lean_ctor_set(v___x_1154_, 1, v_k_1028_);
lean_ctor_set(v___x_1154_, 0, v___x_1037_);
v___x_1158_ = v___x_1154_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1165_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1165_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1165_, 3, v_r_1127_);
lean_ctor_set(v_reuseFailAlloc_1165_, 4, v_r_1127_);
v___x_1158_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1160_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 3, v_r_1127_);
lean_ctor_set(v___x_1149_, 0, v___x_1037_);
v___x_1160_ = v___x_1149_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_k_1146_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_v_1147_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_r_1127_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_r_1127_);
v___x_1160_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
lean_object* v___x_1162_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___x_1160_);
lean_ctor_set(v___x_1033_, 3, v___x_1158_);
lean_ctor_set(v___x_1033_, 2, v_v_1152_);
lean_ctor_set(v___x_1033_, 1, v_k_1151_);
lean_ctor_set(v___x_1033_, 0, v___x_1156_);
v___x_1162_ = v___x_1033_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_k_1151_);
lean_ctor_set(v_reuseFailAlloc_1163_, 2, v_v_1152_);
lean_ctor_set(v_reuseFailAlloc_1163_, 3, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1163_, 4, v___x_1160_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1174_; 
v_r_1174_ = lean_ctor_get(v_r_1031_, 4);
lean_inc(v_r_1174_);
if (lean_obj_tag(v_r_1174_) == 0)
{
lean_object* v_k_1175_; lean_object* v_v_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1187_; 
v_k_1175_ = lean_ctor_get(v_r_1031_, 1);
v_v_1176_ = lean_ctor_get(v_r_1031_, 2);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_r_1031_);
if (v_isSharedCheck_1187_ == 0)
{
lean_object* v_unused_1188_; lean_object* v_unused_1189_; lean_object* v_unused_1190_; 
v_unused_1188_ = lean_ctor_get(v_r_1031_, 4);
lean_dec(v_unused_1188_);
v_unused_1189_ = lean_ctor_get(v_r_1031_, 3);
lean_dec(v_unused_1189_);
v_unused_1190_ = lean_ctor_get(v_r_1031_, 0);
lean_dec(v_unused_1190_);
v___x_1178_ = v_r_1031_;
v_isShared_1179_ = v_isSharedCheck_1187_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_v_1176_);
lean_inc(v_k_1175_);
lean_dec(v_r_1031_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1187_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = lean_unsigned_to_nat(3u);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 4, v_l_1126_);
lean_ctor_set(v___x_1178_, 2, v_v_1029_);
lean_ctor_set(v___x_1178_, 1, v_k_1028_);
lean_ctor_set(v___x_1178_, 0, v___x_1037_);
v___x_1182_ = v___x_1178_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1186_, 3, v_l_1126_);
lean_ctor_set(v_reuseFailAlloc_1186_, 4, v_l_1126_);
v___x_1182_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
lean_object* v___x_1184_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v_r_1174_);
lean_ctor_set(v___x_1033_, 3, v___x_1182_);
lean_ctor_set(v___x_1033_, 2, v_v_1176_);
lean_ctor_set(v___x_1033_, 1, v_k_1175_);
lean_ctor_set(v___x_1033_, 0, v___x_1180_);
v___x_1184_ = v___x_1033_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_k_1175_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_v_1176_);
lean_ctor_set(v_reuseFailAlloc_1185_, 3, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1185_, 4, v_r_1174_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
else
{
lean_object* v_size_1191_; lean_object* v_k_1192_; lean_object* v_v_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1204_; 
v_size_1191_ = lean_ctor_get(v_r_1031_, 0);
v_k_1192_ = lean_ctor_get(v_r_1031_, 1);
v_v_1193_ = lean_ctor_get(v_r_1031_, 2);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_r_1031_);
if (v_isSharedCheck_1204_ == 0)
{
lean_object* v_unused_1205_; lean_object* v_unused_1206_; 
v_unused_1205_ = lean_ctor_get(v_r_1031_, 4);
lean_dec(v_unused_1205_);
v_unused_1206_ = lean_ctor_get(v_r_1031_, 3);
lean_dec(v_unused_1206_);
v___x_1195_ = v_r_1031_;
v_isShared_1196_ = v_isSharedCheck_1204_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_v_1193_);
lean_inc(v_k_1192_);
lean_inc(v_size_1191_);
lean_dec(v_r_1031_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1204_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 3, v_r_1174_);
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_size_1191_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_k_1192_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_v_1193_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_r_1174_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v_r_1174_);
v___x_1198_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1199_ = lean_unsigned_to_nat(2u);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___x_1198_);
lean_ctor_set(v___x_1033_, 3, v_r_1174_);
lean_ctor_set(v___x_1033_, 0, v___x_1199_);
v___x_1201_ = v___x_1033_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
lean_ctor_set(v_reuseFailAlloc_1202_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1202_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1202_, 3, v_r_1174_);
lean_ctor_set(v_reuseFailAlloc_1202_, 4, v___x_1198_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
}
else
{
lean_object* v___x_1208_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 3, v_r_1031_);
lean_ctor_set(v___x_1033_, 0, v___x_1037_);
v___x_1208_ = v___x_1033_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1037_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1209_, 3, v_r_1031_);
lean_ctor_set(v_reuseFailAlloc_1209_, 4, v_r_1031_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1033_);
lean_dec(v_v_1029_);
lean_dec(v_k_1028_);
if (lean_obj_tag(v_l_1030_) == 0)
{
if (lean_obj_tag(v_r_1031_) == 0)
{
lean_object* v_size_1210_; lean_object* v_k_1211_; lean_object* v_v_1212_; lean_object* v_l_1213_; lean_object* v_r_1214_; lean_object* v_size_1215_; lean_object* v_k_1216_; lean_object* v_v_1217_; lean_object* v_l_1218_; lean_object* v_r_1219_; lean_object* v___x_1220_; uint8_t v___x_1221_; 
v_size_1210_ = lean_ctor_get(v_l_1030_, 0);
v_k_1211_ = lean_ctor_get(v_l_1030_, 1);
v_v_1212_ = lean_ctor_get(v_l_1030_, 2);
v_l_1213_ = lean_ctor_get(v_l_1030_, 3);
v_r_1214_ = lean_ctor_get(v_l_1030_, 4);
lean_inc(v_r_1214_);
v_size_1215_ = lean_ctor_get(v_r_1031_, 0);
v_k_1216_ = lean_ctor_get(v_r_1031_, 1);
v_v_1217_ = lean_ctor_get(v_r_1031_, 2);
v_l_1218_ = lean_ctor_get(v_r_1031_, 3);
lean_inc(v_l_1218_);
v_r_1219_ = lean_ctor_get(v_r_1031_, 4);
v___x_1220_ = lean_unsigned_to_nat(1u);
v___x_1221_ = lean_nat_dec_lt(v_size_1210_, v_size_1215_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1357_; 
lean_inc(v_l_1213_);
lean_inc(v_v_1212_);
lean_inc(v_k_1211_);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_l_1030_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; lean_object* v_unused_1359_; lean_object* v_unused_1360_; lean_object* v_unused_1361_; lean_object* v_unused_1362_; 
v_unused_1358_ = lean_ctor_get(v_l_1030_, 4);
lean_dec(v_unused_1358_);
v_unused_1359_ = lean_ctor_get(v_l_1030_, 3);
lean_dec(v_unused_1359_);
v_unused_1360_ = lean_ctor_get(v_l_1030_, 2);
lean_dec(v_unused_1360_);
v_unused_1361_ = lean_ctor_get(v_l_1030_, 1);
lean_dec(v_unused_1361_);
v_unused_1362_ = lean_ctor_get(v_l_1030_, 0);
lean_dec(v_unused_1362_);
v___x_1223_ = v_l_1030_;
v_isShared_1224_ = v_isSharedCheck_1357_;
goto v_resetjp_1222_;
}
else
{
lean_dec(v_l_1030_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1357_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1225_; lean_object* v_tree_1226_; 
v___x_1225_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1211_, v_v_1212_, v_l_1213_, v_r_1214_);
v_tree_1226_ = lean_ctor_get(v___x_1225_, 2);
lean_inc(v_tree_1226_);
if (lean_obj_tag(v_tree_1226_) == 0)
{
lean_object* v_k_1227_; lean_object* v_v_1228_; lean_object* v_size_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v_k_1227_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_k_1227_);
v_v_1228_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_v_1228_);
lean_dec_ref(v___x_1225_);
v_size_1229_ = lean_ctor_get(v_tree_1226_, 0);
v___x_1230_ = lean_unsigned_to_nat(3u);
v___x_1231_ = lean_nat_mul(v___x_1230_, v_size_1229_);
v___x_1232_ = lean_nat_dec_lt(v___x_1231_, v_size_1215_);
lean_dec(v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
lean_dec(v_l_1218_);
v___x_1233_ = lean_nat_add(v___x_1220_, v_size_1229_);
v___x_1234_ = lean_nat_add(v___x_1233_, v_size_1215_);
lean_dec(v___x_1233_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 4, v_r_1031_);
lean_ctor_set(v___x_1223_, 3, v_tree_1226_);
lean_ctor_set(v___x_1223_, 2, v_v_1228_);
lean_ctor_set(v___x_1223_, 1, v_k_1227_);
lean_ctor_set(v___x_1223_, 0, v___x_1234_);
v___x_1236_ = v___x_1223_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_k_1227_);
lean_ctor_set(v_reuseFailAlloc_1237_, 2, v_v_1228_);
lean_ctor_set(v_reuseFailAlloc_1237_, 3, v_tree_1226_);
lean_ctor_set(v_reuseFailAlloc_1237_, 4, v_r_1031_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
else
{
lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1292_; 
lean_inc(v_r_1219_);
lean_inc(v_v_1217_);
lean_inc(v_k_1216_);
lean_inc(v_size_1215_);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_r_1031_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; lean_object* v_unused_1294_; lean_object* v_unused_1295_; lean_object* v_unused_1296_; lean_object* v_unused_1297_; 
v_unused_1293_ = lean_ctor_get(v_r_1031_, 4);
lean_dec(v_unused_1293_);
v_unused_1294_ = lean_ctor_get(v_r_1031_, 3);
lean_dec(v_unused_1294_);
v_unused_1295_ = lean_ctor_get(v_r_1031_, 2);
lean_dec(v_unused_1295_);
v_unused_1296_ = lean_ctor_get(v_r_1031_, 1);
lean_dec(v_unused_1296_);
v_unused_1297_ = lean_ctor_get(v_r_1031_, 0);
lean_dec(v_unused_1297_);
v___x_1239_ = v_r_1031_;
v_isShared_1240_ = v_isSharedCheck_1292_;
goto v_resetjp_1238_;
}
else
{
lean_dec(v_r_1031_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1292_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_size_1241_; lean_object* v_k_1242_; lean_object* v_v_1243_; lean_object* v_l_1244_; lean_object* v_r_1245_; lean_object* v_size_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_size_1241_ = lean_ctor_get(v_l_1218_, 0);
v_k_1242_ = lean_ctor_get(v_l_1218_, 1);
v_v_1243_ = lean_ctor_get(v_l_1218_, 2);
v_l_1244_ = lean_ctor_get(v_l_1218_, 3);
v_r_1245_ = lean_ctor_get(v_l_1218_, 4);
v_size_1246_ = lean_ctor_get(v_r_1219_, 0);
v___x_1247_ = lean_unsigned_to_nat(2u);
v___x_1248_ = lean_nat_mul(v___x_1247_, v_size_1246_);
v___x_1249_ = lean_nat_dec_lt(v_size_1241_, v___x_1248_);
lean_dec(v___x_1248_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1277_; 
lean_inc(v_r_1245_);
lean_inc(v_l_1244_);
lean_inc(v_v_1243_);
lean_inc(v_k_1242_);
v_isSharedCheck_1277_ = !lean_is_exclusive(v_l_1218_);
if (v_isSharedCheck_1277_ == 0)
{
lean_object* v_unused_1278_; lean_object* v_unused_1279_; lean_object* v_unused_1280_; lean_object* v_unused_1281_; lean_object* v_unused_1282_; 
v_unused_1278_ = lean_ctor_get(v_l_1218_, 4);
lean_dec(v_unused_1278_);
v_unused_1279_ = lean_ctor_get(v_l_1218_, 3);
lean_dec(v_unused_1279_);
v_unused_1280_ = lean_ctor_get(v_l_1218_, 2);
lean_dec(v_unused_1280_);
v_unused_1281_ = lean_ctor_get(v_l_1218_, 1);
lean_dec(v_unused_1281_);
v_unused_1282_ = lean_ctor_get(v_l_1218_, 0);
lean_dec(v_unused_1282_);
v___x_1251_ = v_l_1218_;
v_isShared_1252_ = v_isSharedCheck_1277_;
goto v_resetjp_1250_;
}
else
{
lean_dec(v_l_1218_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1277_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1267_; 
v___x_1253_ = lean_nat_add(v___x_1220_, v_size_1229_);
v___x_1254_ = lean_nat_add(v___x_1253_, v_size_1215_);
lean_dec(v_size_1215_);
if (lean_obj_tag(v_l_1244_) == 0)
{
lean_object* v_size_1275_; 
v_size_1275_ = lean_ctor_get(v_l_1244_, 0);
lean_inc(v_size_1275_);
v___y_1267_ = v_size_1275_;
goto v___jp_1266_;
}
else
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_unsigned_to_nat(0u);
v___y_1267_ = v___x_1276_;
goto v___jp_1266_;
}
v___jp_1255_:
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = lean_nat_add(v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec(v___y_1257_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 4, v_r_1219_);
lean_ctor_set(v___x_1251_, 3, v_r_1245_);
lean_ctor_set(v___x_1251_, 2, v_v_1217_);
lean_ctor_set(v___x_1251_, 1, v_k_1216_);
lean_ctor_set(v___x_1251_, 0, v___x_1259_);
v___x_1261_ = v___x_1251_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1265_, 3, v_r_1245_);
lean_ctor_set(v_reuseFailAlloc_1265_, 4, v_r_1219_);
v___x_1261_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1263_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 4, v___x_1261_);
lean_ctor_set(v___x_1239_, 3, v___y_1256_);
lean_ctor_set(v___x_1239_, 2, v_v_1243_);
lean_ctor_set(v___x_1239_, 1, v_k_1242_);
lean_ctor_set(v___x_1239_, 0, v___x_1254_);
v___x_1263_ = v___x_1239_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v___x_1254_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_k_1242_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_v_1243_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v___y_1256_);
lean_ctor_set(v_reuseFailAlloc_1264_, 4, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
v___jp_1266_:
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1268_ = lean_nat_add(v___x_1253_, v___y_1267_);
lean_dec(v___y_1267_);
lean_dec(v___x_1253_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 4, v_l_1244_);
lean_ctor_set(v___x_1223_, 3, v_tree_1226_);
lean_ctor_set(v___x_1223_, 2, v_v_1228_);
lean_ctor_set(v___x_1223_, 1, v_k_1227_);
lean_ctor_set(v___x_1223_, 0, v___x_1268_);
v___x_1270_ = v___x_1223_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_k_1227_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_v_1228_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v_tree_1226_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v_l_1244_);
v___x_1270_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_nat_add(v___x_1220_, v_size_1246_);
if (lean_obj_tag(v_r_1245_) == 0)
{
lean_object* v_size_1272_; 
v_size_1272_ = lean_ctor_get(v_r_1245_, 0);
lean_inc(v_size_1272_);
v___y_1256_ = v___x_1270_;
v___y_1257_ = v___x_1271_;
v___y_1258_ = v_size_1272_;
goto v___jp_1255_;
}
else
{
lean_object* v___x_1273_; 
v___x_1273_ = lean_unsigned_to_nat(0u);
v___y_1256_ = v___x_1270_;
v___y_1257_ = v___x_1271_;
v___y_1258_ = v___x_1273_;
goto v___jp_1255_;
}
}
}
}
}
else
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1283_ = lean_nat_add(v___x_1220_, v_size_1229_);
v___x_1284_ = lean_nat_add(v___x_1283_, v_size_1215_);
lean_dec(v_size_1215_);
v___x_1285_ = lean_nat_add(v___x_1283_, v_size_1241_);
lean_dec(v___x_1283_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 4, v_l_1218_);
lean_ctor_set(v___x_1239_, 3, v_tree_1226_);
lean_ctor_set(v___x_1239_, 2, v_v_1228_);
lean_ctor_set(v___x_1239_, 1, v_k_1227_);
lean_ctor_set(v___x_1239_, 0, v___x_1285_);
v___x_1287_ = v___x_1239_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1285_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_k_1227_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_v_1228_);
lean_ctor_set(v_reuseFailAlloc_1291_, 3, v_tree_1226_);
lean_ctor_set(v_reuseFailAlloc_1291_, 4, v_l_1218_);
v___x_1287_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1289_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 4, v_r_1219_);
lean_ctor_set(v___x_1223_, 3, v___x_1287_);
lean_ctor_set(v___x_1223_, 2, v_v_1217_);
lean_ctor_set(v___x_1223_, 1, v_k_1216_);
lean_ctor_set(v___x_1223_, 0, v___x_1284_);
v___x_1289_ = v___x_1223_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1290_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1290_, 3, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1290_, 4, v_r_1219_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
}
else
{
lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1351_; 
lean_inc(v_r_1219_);
lean_inc(v_v_1217_);
lean_inc(v_k_1216_);
lean_inc(v_size_1215_);
v_isSharedCheck_1351_ = !lean_is_exclusive(v_r_1031_);
if (v_isSharedCheck_1351_ == 0)
{
lean_object* v_unused_1352_; lean_object* v_unused_1353_; lean_object* v_unused_1354_; lean_object* v_unused_1355_; lean_object* v_unused_1356_; 
v_unused_1352_ = lean_ctor_get(v_r_1031_, 4);
lean_dec(v_unused_1352_);
v_unused_1353_ = lean_ctor_get(v_r_1031_, 3);
lean_dec(v_unused_1353_);
v_unused_1354_ = lean_ctor_get(v_r_1031_, 2);
lean_dec(v_unused_1354_);
v_unused_1355_ = lean_ctor_get(v_r_1031_, 1);
lean_dec(v_unused_1355_);
v_unused_1356_ = lean_ctor_get(v_r_1031_, 0);
lean_dec(v_unused_1356_);
v___x_1299_ = v_r_1031_;
v_isShared_1300_ = v_isSharedCheck_1351_;
goto v_resetjp_1298_;
}
else
{
lean_dec(v_r_1031_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1351_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
if (lean_obj_tag(v_l_1218_) == 0)
{
if (lean_obj_tag(v_r_1219_) == 0)
{
lean_object* v_k_1301_; lean_object* v_v_1302_; lean_object* v_size_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1307_; 
v_k_1301_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_k_1301_);
v_v_1302_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_v_1302_);
lean_dec_ref(v___x_1225_);
v_size_1303_ = lean_ctor_get(v_l_1218_, 0);
v___x_1304_ = lean_nat_add(v___x_1220_, v_size_1215_);
lean_dec(v_size_1215_);
v___x_1305_ = lean_nat_add(v___x_1220_, v_size_1303_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 4, v_l_1218_);
lean_ctor_set(v___x_1299_, 3, v_tree_1226_);
lean_ctor_set(v___x_1299_, 2, v_v_1302_);
lean_ctor_set(v___x_1299_, 1, v_k_1301_);
lean_ctor_set(v___x_1299_, 0, v___x_1305_);
v___x_1307_ = v___x_1299_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_k_1301_);
lean_ctor_set(v_reuseFailAlloc_1311_, 2, v_v_1302_);
lean_ctor_set(v_reuseFailAlloc_1311_, 3, v_tree_1226_);
lean_ctor_set(v_reuseFailAlloc_1311_, 4, v_l_1218_);
v___x_1307_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
lean_object* v___x_1309_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 4, v_r_1219_);
lean_ctor_set(v___x_1223_, 3, v___x_1307_);
lean_ctor_set(v___x_1223_, 2, v_v_1217_);
lean_ctor_set(v___x_1223_, 1, v_k_1216_);
lean_ctor_set(v___x_1223_, 0, v___x_1304_);
v___x_1309_ = v___x_1223_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1304_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v_r_1219_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
else
{
lean_object* v_k_1312_; lean_object* v_v_1313_; lean_object* v_k_1314_; lean_object* v_v_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v_size_1215_);
v_k_1312_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_k_1312_);
v_v_1313_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_v_1313_);
lean_dec_ref(v___x_1225_);
v_k_1314_ = lean_ctor_get(v_l_1218_, 1);
v_v_1315_ = lean_ctor_get(v_l_1218_, 2);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_l_1218_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; lean_object* v_unused_1331_; lean_object* v_unused_1332_; 
v_unused_1330_ = lean_ctor_get(v_l_1218_, 4);
lean_dec(v_unused_1330_);
v_unused_1331_ = lean_ctor_get(v_l_1218_, 3);
lean_dec(v_unused_1331_);
v_unused_1332_ = lean_ctor_get(v_l_1218_, 0);
lean_dec(v_unused_1332_);
v___x_1317_ = v_l_1218_;
v_isShared_1318_ = v_isSharedCheck_1329_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_v_1315_);
lean_inc(v_k_1314_);
lean_dec(v_l_1218_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1329_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1319_ = lean_unsigned_to_nat(3u);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v_r_1219_);
lean_ctor_set(v___x_1317_, 3, v_r_1219_);
lean_ctor_set(v___x_1317_, 2, v_v_1313_);
lean_ctor_set(v___x_1317_, 1, v_k_1312_);
lean_ctor_set(v___x_1317_, 0, v___x_1220_);
v___x_1321_ = v___x_1317_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_k_1312_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_v_1313_);
lean_ctor_set(v_reuseFailAlloc_1328_, 3, v_r_1219_);
lean_ctor_set(v_reuseFailAlloc_1328_, 4, v_r_1219_);
v___x_1321_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1323_; 
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 3, v_r_1219_);
lean_ctor_set(v___x_1299_, 0, v___x_1220_);
v___x_1323_ = v___x_1299_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1327_, 3, v_r_1219_);
lean_ctor_set(v_reuseFailAlloc_1327_, 4, v_r_1219_);
v___x_1323_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1325_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 4, v___x_1323_);
lean_ctor_set(v___x_1223_, 3, v___x_1321_);
lean_ctor_set(v___x_1223_, 2, v_v_1315_);
lean_ctor_set(v___x_1223_, 1, v_k_1314_);
lean_ctor_set(v___x_1223_, 0, v___x_1319_);
v___x_1325_ = v___x_1223_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1326_, 1, v_k_1314_);
lean_ctor_set(v_reuseFailAlloc_1326_, 2, v_v_1315_);
lean_ctor_set(v_reuseFailAlloc_1326_, 3, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1326_, 4, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1219_) == 0)
{
lean_object* v_k_1333_; lean_object* v_v_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
lean_dec(v_size_1215_);
v_k_1333_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_k_1333_);
v_v_1334_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_v_1334_);
lean_dec_ref(v___x_1225_);
v___x_1335_ = lean_unsigned_to_nat(3u);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 4, v_l_1218_);
lean_ctor_set(v___x_1299_, 2, v_v_1334_);
lean_ctor_set(v___x_1299_, 1, v_k_1333_);
lean_ctor_set(v___x_1299_, 0, v___x_1220_);
v___x_1337_ = v___x_1299_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_k_1333_);
lean_ctor_set(v_reuseFailAlloc_1341_, 2, v_v_1334_);
lean_ctor_set(v_reuseFailAlloc_1341_, 3, v_l_1218_);
lean_ctor_set(v_reuseFailAlloc_1341_, 4, v_l_1218_);
v___x_1337_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1339_; 
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 4, v_r_1219_);
lean_ctor_set(v___x_1223_, 3, v___x_1337_);
lean_ctor_set(v___x_1223_, 2, v_v_1217_);
lean_ctor_set(v___x_1223_, 1, v_k_1216_);
lean_ctor_set(v___x_1223_, 0, v___x_1335_);
v___x_1339_ = v___x_1223_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v___x_1337_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v_r_1219_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
else
{
lean_object* v_k_1342_; lean_object* v_v_1343_; lean_object* v___x_1345_; 
v_k_1342_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_k_1342_);
v_v_1343_ = lean_ctor_get(v___x_1225_, 1);
lean_inc(v_v_1343_);
lean_dec_ref(v___x_1225_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 3, v_r_1219_);
v___x_1345_ = v___x_1299_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_size_1215_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_k_1216_);
lean_ctor_set(v_reuseFailAlloc_1350_, 2, v_v_1217_);
lean_ctor_set(v_reuseFailAlloc_1350_, 3, v_r_1219_);
lean_ctor_set(v_reuseFailAlloc_1350_, 4, v_r_1219_);
v___x_1345_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1346_; lean_object* v___x_1348_; 
v___x_1346_ = lean_unsigned_to_nat(2u);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 4, v___x_1345_);
lean_ctor_set(v___x_1223_, 3, v_r_1219_);
lean_ctor_set(v___x_1223_, 2, v_v_1343_);
lean_ctor_set(v___x_1223_, 1, v_k_1342_);
lean_ctor_set(v___x_1223_, 0, v___x_1346_);
v___x_1348_ = v___x_1223_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1346_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_k_1342_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_v_1343_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_r_1219_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v___x_1345_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1515_; 
lean_inc(v_r_1219_);
lean_inc(v_v_1217_);
lean_inc(v_k_1216_);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_r_1031_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; lean_object* v_unused_1517_; lean_object* v_unused_1518_; lean_object* v_unused_1519_; lean_object* v_unused_1520_; 
v_unused_1516_ = lean_ctor_get(v_r_1031_, 4);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v_r_1031_, 3);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_r_1031_, 2);
lean_dec(v_unused_1518_);
v_unused_1519_ = lean_ctor_get(v_r_1031_, 1);
lean_dec(v_unused_1519_);
v_unused_1520_ = lean_ctor_get(v_r_1031_, 0);
lean_dec(v_unused_1520_);
v___x_1364_ = v_r_1031_;
v_isShared_1365_ = v_isSharedCheck_1515_;
goto v_resetjp_1363_;
}
else
{
lean_dec(v_r_1031_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1515_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1366_; lean_object* v_tree_1367_; 
v___x_1366_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1216_, v_v_1217_, v_l_1218_, v_r_1219_);
v_tree_1367_ = lean_ctor_get(v___x_1366_, 2);
lean_inc(v_tree_1367_);
if (lean_obj_tag(v_tree_1367_) == 0)
{
lean_object* v_k_1368_; lean_object* v_v_1369_; lean_object* v_size_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_k_1368_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_k_1368_);
v_v_1369_ = lean_ctor_get(v___x_1366_, 1);
lean_inc(v_v_1369_);
lean_dec_ref(v___x_1366_);
v_size_1370_ = lean_ctor_get(v_tree_1367_, 0);
v___x_1371_ = lean_unsigned_to_nat(3u);
v___x_1372_ = lean_nat_mul(v___x_1371_, v_size_1370_);
v___x_1373_ = lean_nat_dec_lt(v___x_1372_, v_size_1210_);
lean_dec(v___x_1372_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
lean_dec(v_r_1214_);
v___x_1374_ = lean_nat_add(v___x_1220_, v_size_1210_);
v___x_1375_ = lean_nat_add(v___x_1374_, v_size_1370_);
lean_dec(v___x_1374_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 4, v_tree_1367_);
lean_ctor_set(v___x_1364_, 3, v_l_1030_);
lean_ctor_set(v___x_1364_, 2, v_v_1369_);
lean_ctor_set(v___x_1364_, 1, v_k_1368_);
lean_ctor_set(v___x_1364_, 0, v___x_1375_);
v___x_1377_ = v___x_1364_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1378_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1378_, 3, v_l_1030_);
lean_ctor_set(v_reuseFailAlloc_1378_, 4, v_tree_1367_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
else
{
lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1444_; 
lean_inc(v_l_1213_);
lean_inc(v_v_1212_);
lean_inc(v_k_1211_);
lean_inc(v_size_1210_);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_l_1030_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; lean_object* v_unused_1446_; lean_object* v_unused_1447_; lean_object* v_unused_1448_; lean_object* v_unused_1449_; 
v_unused_1445_ = lean_ctor_get(v_l_1030_, 4);
lean_dec(v_unused_1445_);
v_unused_1446_ = lean_ctor_get(v_l_1030_, 3);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_l_1030_, 2);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_l_1030_, 1);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_l_1030_, 0);
lean_dec(v_unused_1449_);
v___x_1380_ = v_l_1030_;
v_isShared_1381_ = v_isSharedCheck_1444_;
goto v_resetjp_1379_;
}
else
{
lean_dec(v_l_1030_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1444_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v_size_1382_; lean_object* v_size_1383_; lean_object* v_k_1384_; lean_object* v_v_1385_; lean_object* v_l_1386_; lean_object* v_r_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v_size_1382_ = lean_ctor_get(v_l_1213_, 0);
v_size_1383_ = lean_ctor_get(v_r_1214_, 0);
v_k_1384_ = lean_ctor_get(v_r_1214_, 1);
v_v_1385_ = lean_ctor_get(v_r_1214_, 2);
v_l_1386_ = lean_ctor_get(v_r_1214_, 3);
v_r_1387_ = lean_ctor_get(v_r_1214_, 4);
v___x_1388_ = lean_unsigned_to_nat(2u);
v___x_1389_ = lean_nat_mul(v___x_1388_, v_size_1382_);
v___x_1390_ = lean_nat_dec_lt(v_size_1383_, v___x_1389_);
lean_dec(v___x_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1428_; 
lean_inc(v_r_1387_);
lean_inc(v_l_1386_);
lean_inc(v_v_1385_);
lean_inc(v_k_1384_);
lean_del_object(v___x_1380_);
v_isSharedCheck_1428_ = !lean_is_exclusive(v_r_1214_);
if (v_isSharedCheck_1428_ == 0)
{
lean_object* v_unused_1429_; lean_object* v_unused_1430_; lean_object* v_unused_1431_; lean_object* v_unused_1432_; lean_object* v_unused_1433_; 
v_unused_1429_ = lean_ctor_get(v_r_1214_, 4);
lean_dec(v_unused_1429_);
v_unused_1430_ = lean_ctor_get(v_r_1214_, 3);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_r_1214_, 2);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v_r_1214_, 1);
lean_dec(v_unused_1432_);
v_unused_1433_ = lean_ctor_get(v_r_1214_, 0);
lean_dec(v_unused_1433_);
v___x_1392_ = v_r_1214_;
v_isShared_1393_ = v_isSharedCheck_1428_;
goto v_resetjp_1391_;
}
else
{
lean_dec(v_r_1214_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1428_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___x_1416_; lean_object* v___y_1418_; 
v___x_1394_ = lean_nat_add(v___x_1220_, v_size_1210_);
lean_dec(v_size_1210_);
v___x_1395_ = lean_nat_add(v___x_1394_, v_size_1370_);
lean_dec(v___x_1394_);
v___x_1416_ = lean_nat_add(v___x_1220_, v_size_1382_);
if (lean_obj_tag(v_l_1386_) == 0)
{
lean_object* v_size_1426_; 
v_size_1426_ = lean_ctor_get(v_l_1386_, 0);
lean_inc(v_size_1426_);
v___y_1418_ = v_size_1426_;
goto v___jp_1417_;
}
else
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_unsigned_to_nat(0u);
v___y_1418_ = v___x_1427_;
goto v___jp_1417_;
}
v___jp_1396_:
{
lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1400_ = lean_nat_add(v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec(v___y_1398_);
lean_inc_ref(v_tree_1367_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v_tree_1367_);
lean_ctor_set(v___x_1392_, 3, v_r_1387_);
lean_ctor_set(v___x_1392_, 2, v_v_1369_);
lean_ctor_set(v___x_1392_, 1, v_k_1368_);
lean_ctor_set(v___x_1392_, 0, v___x_1400_);
v___x_1402_ = v___x_1392_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1400_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1415_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1415_, 3, v_r_1387_);
lean_ctor_set(v_reuseFailAlloc_1415_, 4, v_tree_1367_);
v___x_1402_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
v_isSharedCheck_1409_ = !lean_is_exclusive(v_tree_1367_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; lean_object* v_unused_1411_; lean_object* v_unused_1412_; lean_object* v_unused_1413_; lean_object* v_unused_1414_; 
v_unused_1410_ = lean_ctor_get(v_tree_1367_, 4);
lean_dec(v_unused_1410_);
v_unused_1411_ = lean_ctor_get(v_tree_1367_, 3);
lean_dec(v_unused_1411_);
v_unused_1412_ = lean_ctor_get(v_tree_1367_, 2);
lean_dec(v_unused_1412_);
v_unused_1413_ = lean_ctor_get(v_tree_1367_, 1);
lean_dec(v_unused_1413_);
v_unused_1414_ = lean_ctor_get(v_tree_1367_, 0);
lean_dec(v_unused_1414_);
v___x_1404_ = v_tree_1367_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_dec(v_tree_1367_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
lean_ctor_set(v___x_1404_, 4, v___x_1402_);
lean_ctor_set(v___x_1404_, 3, v___y_1397_);
lean_ctor_set(v___x_1404_, 2, v_v_1385_);
lean_ctor_set(v___x_1404_, 1, v_k_1384_);
lean_ctor_set(v___x_1404_, 0, v___x_1395_);
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_k_1384_);
lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_v_1385_);
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v___y_1397_);
lean_ctor_set(v_reuseFailAlloc_1408_, 4, v___x_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
v___jp_1417_:
{
lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1419_ = lean_nat_add(v___x_1416_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec(v___x_1416_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 4, v_l_1386_);
lean_ctor_set(v___x_1364_, 3, v_l_1213_);
lean_ctor_set(v___x_1364_, 2, v_v_1212_);
lean_ctor_set(v___x_1364_, 1, v_k_1211_);
lean_ctor_set(v___x_1364_, 0, v___x_1419_);
v___x_1421_ = v___x_1364_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1419_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_k_1211_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_v_1212_);
lean_ctor_set(v_reuseFailAlloc_1425_, 3, v_l_1213_);
lean_ctor_set(v_reuseFailAlloc_1425_, 4, v_l_1386_);
v___x_1421_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_nat_add(v___x_1220_, v_size_1370_);
if (lean_obj_tag(v_r_1387_) == 0)
{
lean_object* v_size_1423_; 
v_size_1423_ = lean_ctor_get(v_r_1387_, 0);
lean_inc(v_size_1423_);
v___y_1397_ = v___x_1421_;
v___y_1398_ = v___x_1422_;
v___y_1399_ = v_size_1423_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_unsigned_to_nat(0u);
v___y_1397_ = v___x_1421_;
v___y_1398_ = v___x_1422_;
v___y_1399_ = v___x_1424_;
goto v___jp_1396_;
}
}
}
}
}
else
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1434_ = lean_nat_add(v___x_1220_, v_size_1210_);
lean_dec(v_size_1210_);
v___x_1435_ = lean_nat_add(v___x_1434_, v_size_1370_);
lean_dec(v___x_1434_);
v___x_1436_ = lean_nat_add(v___x_1220_, v_size_1370_);
v___x_1437_ = lean_nat_add(v___x_1436_, v_size_1383_);
lean_dec(v___x_1436_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 4, v_tree_1367_);
lean_ctor_set(v___x_1364_, 3, v_r_1214_);
lean_ctor_set(v___x_1364_, 2, v_v_1369_);
lean_ctor_set(v___x_1364_, 1, v_k_1368_);
lean_ctor_set(v___x_1364_, 0, v___x_1437_);
v___x_1439_ = v___x_1364_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_k_1368_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_v_1369_);
lean_ctor_set(v_reuseFailAlloc_1443_, 3, v_r_1214_);
lean_ctor_set(v_reuseFailAlloc_1443_, 4, v_tree_1367_);
v___x_1439_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1441_; 
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 4, v___x_1439_);
lean_ctor_set(v___x_1380_, 0, v___x_1435_);
v___x_1441_ = v___x_1380_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1435_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_k_1211_);
lean_ctor_set(v_reuseFailAlloc_1442_, 2, v_v_1212_);
lean_ctor_set(v_reuseFailAlloc_1442_, 3, v_l_1213_);
lean_ctor_set(v_reuseFailAlloc_1442_, 4, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1213_) == 0)
{
lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1473_; 
lean_inc_ref(v_l_1213_);
lean_inc(v_v_1212_);
lean_inc(v_k_1211_);
lean_inc(v_size_1210_);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_l_1030_);
if (v_isSharedCheck_1473_ == 0)
{
lean_object* v_unused_1474_; lean_object* v_unused_1475_; lean_object* v_unused_1476_; lean_object* v_unused_1477_; lean_object* v_unused_1478_; 
v_unused_1474_ = lean_ctor_get(v_l_1030_, 4);
lean_dec(v_unused_1474_);
v_unused_1475_ = lean_ctor_get(v_l_1030_, 3);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_l_1030_, 2);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_l_1030_, 1);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_l_1030_, 0);
lean_dec(v_unused_1478_);
v___x_1451_ = v_l_1030_;
v_isShared_1452_ = v_isSharedCheck_1473_;
goto v_resetjp_1450_;
}
else
{
lean_dec(v_l_1030_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1473_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
if (lean_obj_tag(v_r_1214_) == 0)
{
lean_object* v_k_1453_; lean_object* v_v_1454_; lean_object* v_size_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
v_k_1453_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_k_1453_);
v_v_1454_ = lean_ctor_get(v___x_1366_, 1);
lean_inc(v_v_1454_);
lean_dec_ref(v___x_1366_);
v_size_1455_ = lean_ctor_get(v_r_1214_, 0);
v___x_1456_ = lean_nat_add(v___x_1220_, v_size_1210_);
lean_dec(v_size_1210_);
v___x_1457_ = lean_nat_add(v___x_1220_, v_size_1455_);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 4, v_tree_1367_);
lean_ctor_set(v___x_1364_, 3, v_r_1214_);
lean_ctor_set(v___x_1364_, 2, v_v_1454_);
lean_ctor_set(v___x_1364_, 1, v_k_1453_);
lean_ctor_set(v___x_1364_, 0, v___x_1457_);
v___x_1459_ = v___x_1364_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_k_1453_);
lean_ctor_set(v_reuseFailAlloc_1463_, 2, v_v_1454_);
lean_ctor_set(v_reuseFailAlloc_1463_, 3, v_r_1214_);
lean_ctor_set(v_reuseFailAlloc_1463_, 4, v_tree_1367_);
v___x_1459_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1461_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 4, v___x_1459_);
lean_ctor_set(v___x_1451_, 0, v___x_1456_);
v___x_1461_ = v___x_1451_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_k_1211_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_v_1212_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_l_1213_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v___x_1459_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
else
{
lean_object* v_k_1464_; lean_object* v_v_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; 
lean_dec(v_size_1210_);
v_k_1464_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_k_1464_);
v_v_1465_ = lean_ctor_get(v___x_1366_, 1);
lean_inc(v_v_1465_);
lean_dec_ref(v___x_1366_);
v___x_1466_ = lean_unsigned_to_nat(3u);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 4, v_r_1214_);
lean_ctor_set(v___x_1364_, 3, v_r_1214_);
lean_ctor_set(v___x_1364_, 2, v_v_1465_);
lean_ctor_set(v___x_1364_, 1, v_k_1464_);
lean_ctor_set(v___x_1364_, 0, v___x_1220_);
v___x_1468_ = v___x_1364_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_k_1464_);
lean_ctor_set(v_reuseFailAlloc_1472_, 2, v_v_1465_);
lean_ctor_set(v_reuseFailAlloc_1472_, 3, v_r_1214_);
lean_ctor_set(v_reuseFailAlloc_1472_, 4, v_r_1214_);
v___x_1468_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1470_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 4, v___x_1468_);
lean_ctor_set(v___x_1451_, 0, v___x_1466_);
v___x_1470_ = v___x_1451_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v_k_1211_);
lean_ctor_set(v_reuseFailAlloc_1471_, 2, v_v_1212_);
lean_ctor_set(v_reuseFailAlloc_1471_, 3, v_l_1213_);
lean_ctor_set(v_reuseFailAlloc_1471_, 4, v___x_1468_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1214_) == 0)
{
lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1503_; 
lean_inc(v_l_1213_);
lean_inc(v_v_1212_);
lean_inc(v_k_1211_);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_l_1030_);
if (v_isSharedCheck_1503_ == 0)
{
lean_object* v_unused_1504_; lean_object* v_unused_1505_; lean_object* v_unused_1506_; lean_object* v_unused_1507_; lean_object* v_unused_1508_; 
v_unused_1504_ = lean_ctor_get(v_l_1030_, 4);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_l_1030_, 3);
lean_dec(v_unused_1505_);
v_unused_1506_ = lean_ctor_get(v_l_1030_, 2);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_l_1030_, 1);
lean_dec(v_unused_1507_);
v_unused_1508_ = lean_ctor_get(v_l_1030_, 0);
lean_dec(v_unused_1508_);
v___x_1480_ = v_l_1030_;
v_isShared_1481_ = v_isSharedCheck_1503_;
goto v_resetjp_1479_;
}
else
{
lean_dec(v_l_1030_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1503_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v_k_1482_; lean_object* v_v_1483_; lean_object* v_k_1484_; lean_object* v_v_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1499_; 
v_k_1482_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_k_1482_);
v_v_1483_ = lean_ctor_get(v___x_1366_, 1);
lean_inc(v_v_1483_);
lean_dec_ref(v___x_1366_);
v_k_1484_ = lean_ctor_get(v_r_1214_, 1);
v_v_1485_ = lean_ctor_get(v_r_1214_, 2);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_r_1214_);
if (v_isSharedCheck_1499_ == 0)
{
lean_object* v_unused_1500_; lean_object* v_unused_1501_; lean_object* v_unused_1502_; 
v_unused_1500_ = lean_ctor_get(v_r_1214_, 4);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_r_1214_, 3);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_r_1214_, 0);
lean_dec(v_unused_1502_);
v___x_1487_ = v_r_1214_;
v_isShared_1488_ = v_isSharedCheck_1499_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_v_1485_);
lean_inc(v_k_1484_);
lean_dec(v_r_1214_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1499_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1489_ = lean_unsigned_to_nat(3u);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 4, v_l_1213_);
lean_ctor_set(v___x_1487_, 3, v_l_1213_);
lean_ctor_set(v___x_1487_, 2, v_v_1212_);
lean_ctor_set(v___x_1487_, 1, v_k_1211_);
lean_ctor_set(v___x_1487_, 0, v___x_1220_);
v___x_1491_ = v___x_1487_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v_k_1211_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_v_1212_);
lean_ctor_set(v_reuseFailAlloc_1498_, 3, v_l_1213_);
lean_ctor_set(v_reuseFailAlloc_1498_, 4, v_l_1213_);
v___x_1491_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
lean_object* v___x_1493_; 
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 4, v_l_1213_);
lean_ctor_set(v___x_1364_, 3, v_l_1213_);
lean_ctor_set(v___x_1364_, 2, v_v_1483_);
lean_ctor_set(v___x_1364_, 1, v_k_1482_);
lean_ctor_set(v___x_1364_, 0, v___x_1220_);
v___x_1493_ = v___x_1364_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1497_, 1, v_k_1482_);
lean_ctor_set(v_reuseFailAlloc_1497_, 2, v_v_1483_);
lean_ctor_set(v_reuseFailAlloc_1497_, 3, v_l_1213_);
lean_ctor_set(v_reuseFailAlloc_1497_, 4, v_l_1213_);
v___x_1493_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
lean_object* v___x_1495_; 
if (v_isShared_1481_ == 0)
{
lean_ctor_set(v___x_1480_, 4, v___x_1493_);
lean_ctor_set(v___x_1480_, 3, v___x_1491_);
lean_ctor_set(v___x_1480_, 2, v_v_1485_);
lean_ctor_set(v___x_1480_, 1, v_k_1484_);
lean_ctor_set(v___x_1480_, 0, v___x_1489_);
v___x_1495_ = v___x_1480_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v_k_1484_);
lean_ctor_set(v_reuseFailAlloc_1496_, 2, v_v_1485_);
lean_ctor_set(v_reuseFailAlloc_1496_, 3, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1496_, 4, v___x_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
}
else
{
lean_object* v_k_1509_; lean_object* v_v_1510_; lean_object* v___x_1511_; lean_object* v___x_1513_; 
v_k_1509_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_k_1509_);
v_v_1510_ = lean_ctor_get(v___x_1366_, 1);
lean_inc(v_v_1510_);
lean_dec_ref(v___x_1366_);
v___x_1511_ = lean_unsigned_to_nat(2u);
if (v_isShared_1365_ == 0)
{
lean_ctor_set(v___x_1364_, 4, v_r_1214_);
lean_ctor_set(v___x_1364_, 3, v_l_1030_);
lean_ctor_set(v___x_1364_, 2, v_v_1510_);
lean_ctor_set(v___x_1364_, 1, v_k_1509_);
lean_ctor_set(v___x_1364_, 0, v___x_1511_);
v___x_1513_ = v___x_1364_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_k_1509_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_v_1510_);
lean_ctor_set(v_reuseFailAlloc_1514_, 3, v_l_1030_);
lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_r_1214_);
v___x_1513_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
return v___x_1513_;
}
}
}
}
}
}
}
else
{
return v_l_1030_;
}
}
else
{
return v_r_1031_;
}
}
default: 
{
lean_object* v_impl_1521_; lean_object* v___x_1522_; 
v_impl_1521_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1026_, v_r_1031_);
v___x_1522_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1521_) == 0)
{
if (lean_obj_tag(v_l_1030_) == 0)
{
lean_object* v_size_1523_; lean_object* v_size_1524_; lean_object* v_k_1525_; lean_object* v_v_1526_; lean_object* v_l_1527_; lean_object* v_r_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; uint8_t v___x_1531_; 
v_size_1523_ = lean_ctor_get(v_impl_1521_, 0);
lean_inc(v_size_1523_);
v_size_1524_ = lean_ctor_get(v_l_1030_, 0);
v_k_1525_ = lean_ctor_get(v_l_1030_, 1);
v_v_1526_ = lean_ctor_get(v_l_1030_, 2);
v_l_1527_ = lean_ctor_get(v_l_1030_, 3);
v_r_1528_ = lean_ctor_get(v_l_1030_, 4);
lean_inc(v_r_1528_);
v___x_1529_ = lean_unsigned_to_nat(3u);
v___x_1530_ = lean_nat_mul(v___x_1529_, v_size_1523_);
v___x_1531_ = lean_nat_dec_lt(v___x_1530_, v_size_1524_);
lean_dec(v___x_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1535_; 
lean_dec(v_r_1528_);
v___x_1532_ = lean_nat_add(v___x_1522_, v_size_1524_);
v___x_1533_ = lean_nat_add(v___x_1532_, v_size_1523_);
lean_dec(v_size_1523_);
lean_dec(v___x_1532_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v_impl_1521_);
lean_ctor_set(v___x_1033_, 0, v___x_1533_);
v___x_1535_ = v___x_1033_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1536_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1536_, 3, v_l_1030_);
lean_ctor_set(v_reuseFailAlloc_1536_, 4, v_impl_1521_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
else
{
lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1602_; 
lean_inc(v_l_1527_);
lean_inc(v_v_1526_);
lean_inc(v_k_1525_);
lean_inc(v_size_1524_);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_l_1030_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; lean_object* v_unused_1604_; lean_object* v_unused_1605_; lean_object* v_unused_1606_; lean_object* v_unused_1607_; 
v_unused_1603_ = lean_ctor_get(v_l_1030_, 4);
lean_dec(v_unused_1603_);
v_unused_1604_ = lean_ctor_get(v_l_1030_, 3);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v_l_1030_, 2);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v_l_1030_, 1);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_l_1030_, 0);
lean_dec(v_unused_1607_);
v___x_1538_ = v_l_1030_;
v_isShared_1539_ = v_isSharedCheck_1602_;
goto v_resetjp_1537_;
}
else
{
lean_dec(v_l_1030_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1602_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v_size_1540_; lean_object* v_size_1541_; lean_object* v_k_1542_; lean_object* v_v_1543_; lean_object* v_l_1544_; lean_object* v_r_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_size_1540_ = lean_ctor_get(v_l_1527_, 0);
v_size_1541_ = lean_ctor_get(v_r_1528_, 0);
v_k_1542_ = lean_ctor_get(v_r_1528_, 1);
v_v_1543_ = lean_ctor_get(v_r_1528_, 2);
v_l_1544_ = lean_ctor_get(v_r_1528_, 3);
v_r_1545_ = lean_ctor_get(v_r_1528_, 4);
v___x_1546_ = lean_unsigned_to_nat(2u);
v___x_1547_ = lean_nat_mul(v___x_1546_, v_size_1540_);
v___x_1548_ = lean_nat_dec_lt(v_size_1541_, v___x_1547_);
lean_dec(v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1577_; 
lean_inc(v_r_1545_);
lean_inc(v_l_1544_);
lean_inc(v_v_1543_);
lean_inc(v_k_1542_);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_r_1528_);
if (v_isSharedCheck_1577_ == 0)
{
lean_object* v_unused_1578_; lean_object* v_unused_1579_; lean_object* v_unused_1580_; lean_object* v_unused_1581_; lean_object* v_unused_1582_; 
v_unused_1578_ = lean_ctor_get(v_r_1528_, 4);
lean_dec(v_unused_1578_);
v_unused_1579_ = lean_ctor_get(v_r_1528_, 3);
lean_dec(v_unused_1579_);
v_unused_1580_ = lean_ctor_get(v_r_1528_, 2);
lean_dec(v_unused_1580_);
v_unused_1581_ = lean_ctor_get(v_r_1528_, 1);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v_r_1528_, 0);
lean_dec(v_unused_1582_);
v___x_1550_ = v_r_1528_;
v_isShared_1551_ = v_isSharedCheck_1577_;
goto v_resetjp_1549_;
}
else
{
lean_dec(v_r_1528_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1577_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___y_1555_; lean_object* v___y_1556_; lean_object* v___y_1557_; lean_object* v___x_1565_; lean_object* v___y_1567_; 
v___x_1552_ = lean_nat_add(v___x_1522_, v_size_1524_);
lean_dec(v_size_1524_);
v___x_1553_ = lean_nat_add(v___x_1552_, v_size_1523_);
lean_dec(v___x_1552_);
v___x_1565_ = lean_nat_add(v___x_1522_, v_size_1540_);
if (lean_obj_tag(v_l_1544_) == 0)
{
lean_object* v_size_1575_; 
v_size_1575_ = lean_ctor_get(v_l_1544_, 0);
lean_inc(v_size_1575_);
v___y_1567_ = v_size_1575_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_unsigned_to_nat(0u);
v___y_1567_ = v___x_1576_;
goto v___jp_1566_;
}
v___jp_1554_:
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1558_ = lean_nat_add(v___y_1555_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec(v___y_1555_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 4, v_impl_1521_);
lean_ctor_set(v___x_1550_, 3, v_r_1545_);
lean_ctor_set(v___x_1550_, 2, v_v_1029_);
lean_ctor_set(v___x_1550_, 1, v_k_1028_);
lean_ctor_set(v___x_1550_, 0, v___x_1558_);
v___x_1560_ = v___x_1550_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1564_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1564_, 3, v_r_1545_);
lean_ctor_set(v_reuseFailAlloc_1564_, 4, v_impl_1521_);
v___x_1560_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
lean_object* v___x_1562_; 
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v___x_1560_);
lean_ctor_set(v___x_1538_, 3, v___y_1556_);
lean_ctor_set(v___x_1538_, 2, v_v_1543_);
lean_ctor_set(v___x_1538_, 1, v_k_1542_);
lean_ctor_set(v___x_1538_, 0, v___x_1553_);
v___x_1562_ = v___x_1538_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_k_1542_);
lean_ctor_set(v_reuseFailAlloc_1563_, 2, v_v_1543_);
lean_ctor_set(v_reuseFailAlloc_1563_, 3, v___y_1556_);
lean_ctor_set(v_reuseFailAlloc_1563_, 4, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
v___jp_1566_:
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = lean_nat_add(v___x_1565_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec(v___x_1565_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v_l_1544_);
lean_ctor_set(v___x_1033_, 3, v_l_1527_);
lean_ctor_set(v___x_1033_, 2, v_v_1526_);
lean_ctor_set(v___x_1033_, 1, v_k_1525_);
lean_ctor_set(v___x_1033_, 0, v___x_1568_);
v___x_1570_ = v___x_1033_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_k_1525_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v_v_1526_);
lean_ctor_set(v_reuseFailAlloc_1574_, 3, v_l_1527_);
lean_ctor_set(v_reuseFailAlloc_1574_, 4, v_l_1544_);
v___x_1570_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_nat_add(v___x_1522_, v_size_1523_);
lean_dec(v_size_1523_);
if (lean_obj_tag(v_r_1545_) == 0)
{
lean_object* v_size_1572_; 
v_size_1572_ = lean_ctor_get(v_r_1545_, 0);
lean_inc(v_size_1572_);
v___y_1555_ = v___x_1571_;
v___y_1556_ = v___x_1570_;
v___y_1557_ = v_size_1572_;
goto v___jp_1554_;
}
else
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_unsigned_to_nat(0u);
v___y_1555_ = v___x_1571_;
v___y_1556_ = v___x_1570_;
v___y_1557_ = v___x_1573_;
goto v___jp_1554_;
}
}
}
}
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
lean_del_object(v___x_1033_);
v___x_1583_ = lean_nat_add(v___x_1522_, v_size_1524_);
lean_dec(v_size_1524_);
v___x_1584_ = lean_nat_add(v___x_1583_, v_size_1523_);
lean_dec(v___x_1583_);
v___x_1585_ = lean_nat_add(v___x_1522_, v_size_1523_);
lean_dec(v_size_1523_);
v___x_1586_ = lean_nat_add(v___x_1585_, v_size_1541_);
lean_dec(v___x_1585_);
lean_inc_ref(v_impl_1521_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 4, v_impl_1521_);
lean_ctor_set(v___x_1538_, 3, v_r_1528_);
lean_ctor_set(v___x_1538_, 2, v_v_1029_);
lean_ctor_set(v___x_1538_, 1, v_k_1028_);
lean_ctor_set(v___x_1538_, 0, v___x_1586_);
v___x_1588_ = v___x_1538_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_r_1528_);
lean_ctor_set(v_reuseFailAlloc_1601_, 4, v_impl_1521_);
v___x_1588_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
v_isSharedCheck_1595_ = !lean_is_exclusive(v_impl_1521_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; lean_object* v_unused_1600_; 
v_unused_1596_ = lean_ctor_get(v_impl_1521_, 4);
lean_dec(v_unused_1596_);
v_unused_1597_ = lean_ctor_get(v_impl_1521_, 3);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_impl_1521_, 2);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_impl_1521_, 1);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_impl_1521_, 0);
lean_dec(v_unused_1600_);
v___x_1590_ = v_impl_1521_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_dec(v_impl_1521_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
lean_ctor_set(v___x_1590_, 4, v___x_1588_);
lean_ctor_set(v___x_1590_, 3, v_l_1527_);
lean_ctor_set(v___x_1590_, 2, v_v_1526_);
lean_ctor_set(v___x_1590_, 1, v_k_1525_);
lean_ctor_set(v___x_1590_, 0, v___x_1584_);
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_k_1525_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_v_1526_);
lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_l_1527_);
lean_ctor_set(v_reuseFailAlloc_1594_, 4, v___x_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1608_; lean_object* v___x_1609_; lean_object* v___x_1611_; 
v_size_1608_ = lean_ctor_get(v_impl_1521_, 0);
lean_inc(v_size_1608_);
v___x_1609_ = lean_nat_add(v___x_1522_, v_size_1608_);
lean_dec(v_size_1608_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v_impl_1521_);
lean_ctor_set(v___x_1033_, 0, v___x_1609_);
v___x_1611_ = v___x_1033_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
lean_ctor_set(v_reuseFailAlloc_1612_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1612_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1612_, 3, v_l_1030_);
lean_ctor_set(v_reuseFailAlloc_1612_, 4, v_impl_1521_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
else
{
if (lean_obj_tag(v_l_1030_) == 0)
{
lean_object* v_l_1613_; 
v_l_1613_ = lean_ctor_get(v_l_1030_, 3);
if (lean_obj_tag(v_l_1613_) == 0)
{
lean_object* v_r_1614_; 
lean_inc_ref(v_l_1613_);
v_r_1614_ = lean_ctor_get(v_l_1030_, 4);
lean_inc(v_r_1614_);
if (lean_obj_tag(v_r_1614_) == 0)
{
lean_object* v_size_1615_; lean_object* v_k_1616_; lean_object* v_v_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1630_; 
v_size_1615_ = lean_ctor_get(v_l_1030_, 0);
v_k_1616_ = lean_ctor_get(v_l_1030_, 1);
v_v_1617_ = lean_ctor_get(v_l_1030_, 2);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_l_1030_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; lean_object* v_unused_1632_; 
v_unused_1631_ = lean_ctor_get(v_l_1030_, 4);
lean_dec(v_unused_1631_);
v_unused_1632_ = lean_ctor_get(v_l_1030_, 3);
lean_dec(v_unused_1632_);
v___x_1619_ = v_l_1030_;
v_isShared_1620_ = v_isSharedCheck_1630_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_v_1617_);
lean_inc(v_k_1616_);
lean_inc(v_size_1615_);
lean_dec(v_l_1030_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1630_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v_size_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1625_; 
v_size_1621_ = lean_ctor_get(v_r_1614_, 0);
v___x_1622_ = lean_nat_add(v___x_1522_, v_size_1615_);
lean_dec(v_size_1615_);
v___x_1623_ = lean_nat_add(v___x_1522_, v_size_1621_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 4, v_impl_1521_);
lean_ctor_set(v___x_1619_, 3, v_r_1614_);
lean_ctor_set(v___x_1619_, 2, v_v_1029_);
lean_ctor_set(v___x_1619_, 1, v_k_1028_);
lean_ctor_set(v___x_1619_, 0, v___x_1623_);
v___x_1625_ = v___x_1619_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1623_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1629_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1629_, 3, v_r_1614_);
lean_ctor_set(v_reuseFailAlloc_1629_, 4, v_impl_1521_);
v___x_1625_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
lean_object* v___x_1627_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___x_1625_);
lean_ctor_set(v___x_1033_, 3, v_l_1613_);
lean_ctor_set(v___x_1033_, 2, v_v_1617_);
lean_ctor_set(v___x_1033_, 1, v_k_1616_);
lean_ctor_set(v___x_1033_, 0, v___x_1622_);
v___x_1627_ = v___x_1033_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1622_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_k_1616_);
lean_ctor_set(v_reuseFailAlloc_1628_, 2, v_v_1617_);
lean_ctor_set(v_reuseFailAlloc_1628_, 3, v_l_1613_);
lean_ctor_set(v_reuseFailAlloc_1628_, 4, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v_k_1633_; lean_object* v_v_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1645_; 
v_k_1633_ = lean_ctor_get(v_l_1030_, 1);
v_v_1634_ = lean_ctor_get(v_l_1030_, 2);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_l_1030_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; lean_object* v_unused_1647_; lean_object* v_unused_1648_; 
v_unused_1646_ = lean_ctor_get(v_l_1030_, 4);
lean_dec(v_unused_1646_);
v_unused_1647_ = lean_ctor_get(v_l_1030_, 3);
lean_dec(v_unused_1647_);
v_unused_1648_ = lean_ctor_get(v_l_1030_, 0);
lean_dec(v_unused_1648_);
v___x_1636_ = v_l_1030_;
v_isShared_1637_ = v_isSharedCheck_1645_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_v_1634_);
lean_inc(v_k_1633_);
lean_dec(v_l_1030_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1645_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1640_; 
v___x_1638_ = lean_unsigned_to_nat(3u);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 3, v_r_1614_);
lean_ctor_set(v___x_1636_, 2, v_v_1029_);
lean_ctor_set(v___x_1636_, 1, v_k_1028_);
lean_ctor_set(v___x_1636_, 0, v___x_1522_);
v___x_1640_ = v___x_1636_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_r_1614_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v_r_1614_);
v___x_1640_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
lean_object* v___x_1642_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___x_1640_);
lean_ctor_set(v___x_1033_, 3, v_l_1613_);
lean_ctor_set(v___x_1033_, 2, v_v_1634_);
lean_ctor_set(v___x_1033_, 1, v_k_1633_);
lean_ctor_set(v___x_1033_, 0, v___x_1638_);
v___x_1642_ = v___x_1033_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_k_1633_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_v_1634_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_l_1613_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v___x_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
}
else
{
lean_object* v_r_1649_; 
v_r_1649_ = lean_ctor_get(v_l_1030_, 4);
lean_inc(v_r_1649_);
if (lean_obj_tag(v_r_1649_) == 0)
{
lean_object* v_k_1650_; lean_object* v_v_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1674_; 
lean_inc(v_l_1613_);
v_k_1650_ = lean_ctor_get(v_l_1030_, 1);
v_v_1651_ = lean_ctor_get(v_l_1030_, 2);
v_isSharedCheck_1674_ = !lean_is_exclusive(v_l_1030_);
if (v_isSharedCheck_1674_ == 0)
{
lean_object* v_unused_1675_; lean_object* v_unused_1676_; lean_object* v_unused_1677_; 
v_unused_1675_ = lean_ctor_get(v_l_1030_, 4);
lean_dec(v_unused_1675_);
v_unused_1676_ = lean_ctor_get(v_l_1030_, 3);
lean_dec(v_unused_1676_);
v_unused_1677_ = lean_ctor_get(v_l_1030_, 0);
lean_dec(v_unused_1677_);
v___x_1653_ = v_l_1030_;
v_isShared_1654_ = v_isSharedCheck_1674_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_v_1651_);
lean_inc(v_k_1650_);
lean_dec(v_l_1030_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1674_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v_k_1655_; lean_object* v_v_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1670_; 
v_k_1655_ = lean_ctor_get(v_r_1649_, 1);
v_v_1656_ = lean_ctor_get(v_r_1649_, 2);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_r_1649_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; lean_object* v_unused_1672_; lean_object* v_unused_1673_; 
v_unused_1671_ = lean_ctor_get(v_r_1649_, 4);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v_r_1649_, 3);
lean_dec(v_unused_1672_);
v_unused_1673_ = lean_ctor_get(v_r_1649_, 0);
lean_dec(v_unused_1673_);
v___x_1658_ = v_r_1649_;
v_isShared_1659_ = v_isSharedCheck_1670_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_v_1656_);
lean_inc(v_k_1655_);
lean_dec(v_r_1649_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1670_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1660_; lean_object* v___x_1662_; 
v___x_1660_ = lean_unsigned_to_nat(3u);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 4, v_l_1613_);
lean_ctor_set(v___x_1658_, 3, v_l_1613_);
lean_ctor_set(v___x_1658_, 2, v_v_1651_);
lean_ctor_set(v___x_1658_, 1, v_k_1650_);
lean_ctor_set(v___x_1658_, 0, v___x_1522_);
v___x_1662_ = v___x_1658_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_k_1650_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_v_1651_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v_l_1613_);
lean_ctor_set(v_reuseFailAlloc_1669_, 4, v_l_1613_);
v___x_1662_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
lean_object* v___x_1664_; 
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 4, v_l_1613_);
lean_ctor_set(v___x_1653_, 2, v_v_1029_);
lean_ctor_set(v___x_1653_, 1, v_k_1028_);
lean_ctor_set(v___x_1653_, 0, v___x_1522_);
v___x_1664_ = v___x_1653_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1668_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1668_, 3, v_l_1613_);
lean_ctor_set(v_reuseFailAlloc_1668_, 4, v_l_1613_);
v___x_1664_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1666_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v___x_1664_);
lean_ctor_set(v___x_1033_, 3, v___x_1662_);
lean_ctor_set(v___x_1033_, 2, v_v_1656_);
lean_ctor_set(v___x_1033_, 1, v_k_1655_);
lean_ctor_set(v___x_1033_, 0, v___x_1660_);
v___x_1666_ = v___x_1033_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1660_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_k_1655_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_v_1656_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v___x_1662_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
}
}
else
{
lean_object* v___x_1678_; lean_object* v___x_1680_; 
v___x_1678_ = lean_unsigned_to_nat(2u);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v_r_1649_);
lean_ctor_set(v___x_1033_, 0, v___x_1678_);
v___x_1680_ = v___x_1033_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1678_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1681_, 3, v_l_1030_);
lean_ctor_set(v_reuseFailAlloc_1681_, 4, v_r_1649_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
else
{
lean_object* v___x_1683_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 4, v_l_1030_);
lean_ctor_set(v___x_1033_, 0, v___x_1522_);
v___x_1683_ = v___x_1033_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1522_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_k_1028_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_v_1029_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v_l_1030_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v_l_1030_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
}
}
else
{
return v_t_1027_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_1687_, lean_object* v_t_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1687_, v_t_1688_);
lean_dec(v_k_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_1690_, lean_object* v_declName_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v___x_1695_; lean_object* v_ext_1696_; lean_object* v_toEnvExtension_1697_; lean_object* v_env_1698_; lean_object* v_asyncMode_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___y_1703_; lean_object* v_funCC_1729_; uint8_t v___x_1730_; 
v___x_1695_ = lean_st_ref_get(v_a_1693_);
v_ext_1696_ = lean_ctor_get(v_ext_1690_, 1);
v_toEnvExtension_1697_ = lean_ctor_get(v_ext_1696_, 0);
v_env_1698_ = lean_ctor_get(v___x_1695_, 0);
lean_inc_ref(v_env_1698_);
lean_dec(v___x_1695_);
v_asyncMode_1699_ = lean_ctor_get(v_toEnvExtension_1697_, 2);
v___x_1700_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1701_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1700_, v_ext_1690_, v_env_1698_, v_asyncMode_1699_);
v_funCC_1729_ = lean_ctor_get(v___x_1701_, 2);
lean_inc(v_funCC_1729_);
v___x_1730_ = l_Lean_NameSet_contains(v_funCC_1729_, v_declName_1691_);
lean_dec(v_funCC_1729_);
if (v___x_1730_ == 0)
{
lean_object* v___x_1731_; 
lean_inc(v_declName_1691_);
v___x_1731_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_1691_, v_a_1692_, v_a_1693_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_dec_ref(v___x_1731_);
v___y_1703_ = v_a_1693_;
goto v___jp_1702_;
}
else
{
lean_dec(v___x_1701_);
lean_dec(v_declName_1691_);
lean_dec_ref(v_ext_1690_);
return v___x_1731_;
}
}
else
{
v___y_1703_ = v_a_1693_;
goto v___jp_1702_;
}
v___jp_1702_:
{
lean_object* v_funCC_1704_; lean_object* v___x_1705_; lean_object* v_env_1706_; lean_object* v_nextMacroScope_1707_; lean_object* v_ngen_1708_; lean_object* v_auxDeclNGen_1709_; lean_object* v_traceState_1710_; lean_object* v_messages_1711_; lean_object* v_infoState_1712_; lean_object* v_snapshotTasks_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1727_; 
v_funCC_1704_ = lean_ctor_get(v___x_1701_, 2);
lean_inc(v_funCC_1704_);
lean_dec(v___x_1701_);
v___x_1705_ = lean_st_ref_take(v___y_1703_);
v_env_1706_ = lean_ctor_get(v___x_1705_, 0);
v_nextMacroScope_1707_ = lean_ctor_get(v___x_1705_, 1);
v_ngen_1708_ = lean_ctor_get(v___x_1705_, 2);
v_auxDeclNGen_1709_ = lean_ctor_get(v___x_1705_, 3);
v_traceState_1710_ = lean_ctor_get(v___x_1705_, 4);
v_messages_1711_ = lean_ctor_get(v___x_1705_, 6);
v_infoState_1712_ = lean_ctor_get(v___x_1705_, 7);
v_snapshotTasks_1713_ = lean_ctor_get(v___x_1705_, 8);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1727_ == 0)
{
lean_object* v_unused_1728_; 
v_unused_1728_ = lean_ctor_get(v___x_1705_, 5);
lean_dec(v_unused_1728_);
v___x_1715_ = v___x_1705_;
v_isShared_1716_ = v_isSharedCheck_1727_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_snapshotTasks_1713_);
lean_inc(v_infoState_1712_);
lean_inc(v_messages_1711_);
lean_inc(v_traceState_1710_);
lean_inc(v_auxDeclNGen_1709_);
lean_inc(v_ngen_1708_);
lean_inc(v_nextMacroScope_1707_);
lean_inc(v_env_1706_);
lean_dec(v___x_1705_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1727_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___f_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1717_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_1691_, v_funCC_1704_);
lean_dec(v_declName_1691_);
v___f_1718_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_1718_, 0, v___x_1717_);
v___x_1719_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1690_, v_env_1706_, v___f_1718_);
v___x_1720_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 5, v___x_1720_);
lean_ctor_set(v___x_1715_, 0, v___x_1719_);
v___x_1722_ = v___x_1715_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_nextMacroScope_1707_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v_ngen_1708_);
lean_ctor_set(v_reuseFailAlloc_1726_, 3, v_auxDeclNGen_1709_);
lean_ctor_set(v_reuseFailAlloc_1726_, 4, v_traceState_1710_);
lean_ctor_set(v_reuseFailAlloc_1726_, 5, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1726_, 6, v_messages_1711_);
lean_ctor_set(v_reuseFailAlloc_1726_, 7, v_infoState_1712_);
lean_ctor_set(v_reuseFailAlloc_1726_, 8, v_snapshotTasks_1713_);
v___x_1722_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v___x_1723_ = lean_st_ref_set(v___y_1703_, v___x_1722_);
v___x_1724_ = lean_box(0);
v___x_1725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1725_, 0, v___x_1724_);
return v___x_1725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_1732_, lean_object* v_declName_1733_, lean_object* v_a_1734_, lean_object* v_a_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_1732_, v_declName_1733_, v_a_1734_, v_a_1735_);
lean_dec(v_a_1735_);
lean_dec_ref(v_a_1734_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_1738_, lean_object* v_k_1739_, lean_object* v_t_1740_, lean_object* v_h_1741_){
_start:
{
lean_object* v___x_1742_; 
v___x_1742_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1739_, v_t_1740_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_1743_, lean_object* v_k_1744_, lean_object* v_t_1745_, lean_object* v_h_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_1743_, v_k_1744_, v_t_1745_, v_h_1746_);
lean_dec(v_k_1744_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_1748_, lean_object* v_s_1749_){
_start:
{
lean_object* v_casesTypes_1750_; lean_object* v_extThms_1751_; lean_object* v_funCC_1752_; lean_object* v_inj_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
v_casesTypes_1750_ = lean_ctor_get(v_s_1749_, 0);
v_extThms_1751_ = lean_ctor_get(v_s_1749_, 1);
v_funCC_1752_ = lean_ctor_get(v_s_1749_, 2);
v_inj_1753_ = lean_ctor_get(v_s_1749_, 4);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_s_1749_);
if (v_isSharedCheck_1760_ == 0)
{
lean_object* v_unused_1761_; 
v_unused_1761_ = lean_ctor_get(v_s_1749_, 3);
lean_dec(v_unused_1761_);
v___x_1755_ = v_s_1749_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_inj_1753_);
lean_inc(v_funCC_1752_);
lean_inc(v_extThms_1751_);
lean_inc(v_casesTypes_1750_);
lean_dec(v_s_1749_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 3, v_a_1748_);
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_casesTypes_1750_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_extThms_1751_);
lean_ctor_set(v_reuseFailAlloc_1759_, 2, v_funCC_1752_);
lean_ctor_set(v_reuseFailAlloc_1759_, 3, v_a_1748_);
lean_ctor_set(v_reuseFailAlloc_1759_, 4, v_inj_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0(void){
_start:
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_1763_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1763_, 0, v___x_1762_);
lean_ctor_set(v___x_1763_, 1, v___x_1762_);
lean_ctor_set(v___x_1763_, 2, v___x_1762_);
lean_ctor_set(v___x_1763_, 3, v___x_1762_);
lean_ctor_set(v___x_1763_, 4, v___x_1762_);
lean_ctor_set(v___x_1763_, 5, v___x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_1764_, lean_object* v_declName_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v___x_1771_; lean_object* v_ext_1772_; lean_object* v_toEnvExtension_1773_; lean_object* v_env_1774_; lean_object* v_asyncMode_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v_ematch_1778_; lean_object* v___x_1779_; 
v___x_1771_ = lean_st_ref_get(v_a_1769_);
v_ext_1772_ = lean_ctor_get(v_ext_1764_, 1);
v_toEnvExtension_1773_ = lean_ctor_get(v_ext_1772_, 0);
v_env_1774_ = lean_ctor_get(v___x_1771_, 0);
lean_inc_ref(v_env_1774_);
lean_dec(v___x_1771_);
v_asyncMode_1775_ = lean_ctor_get(v_toEnvExtension_1773_, 2);
v___x_1776_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1777_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1776_, v_ext_1764_, v_env_1774_, v_asyncMode_1775_);
v_ematch_1778_ = lean_ctor_get(v___x_1777_, 3);
lean_inc_ref(v_ematch_1778_);
lean_dec(v___x_1777_);
v___x_1779_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_1778_, v_declName_1765_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1824_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1782_ = v___x_1779_;
v_isShared_1783_ = v_isSharedCheck_1824_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1779_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1824_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1784_; lean_object* v_env_1785_; lean_object* v_nextMacroScope_1786_; lean_object* v_ngen_1787_; lean_object* v_auxDeclNGen_1788_; lean_object* v_traceState_1789_; lean_object* v_messages_1790_; lean_object* v_infoState_1791_; lean_object* v_snapshotTasks_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1822_; 
v___x_1784_ = lean_st_ref_take(v_a_1769_);
v_env_1785_ = lean_ctor_get(v___x_1784_, 0);
v_nextMacroScope_1786_ = lean_ctor_get(v___x_1784_, 1);
v_ngen_1787_ = lean_ctor_get(v___x_1784_, 2);
v_auxDeclNGen_1788_ = lean_ctor_get(v___x_1784_, 3);
v_traceState_1789_ = lean_ctor_get(v___x_1784_, 4);
v_messages_1790_ = lean_ctor_get(v___x_1784_, 6);
v_infoState_1791_ = lean_ctor_get(v___x_1784_, 7);
v_snapshotTasks_1792_ = lean_ctor_get(v___x_1784_, 8);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1822_ == 0)
{
lean_object* v_unused_1823_; 
v_unused_1823_ = lean_ctor_get(v___x_1784_, 5);
lean_dec(v_unused_1823_);
v___x_1794_ = v___x_1784_;
v_isShared_1795_ = v_isSharedCheck_1822_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_snapshotTasks_1792_);
lean_inc(v_infoState_1791_);
lean_inc(v_messages_1790_);
lean_inc(v_traceState_1789_);
lean_inc(v_auxDeclNGen_1788_);
lean_inc(v_ngen_1787_);
lean_inc(v_nextMacroScope_1786_);
lean_inc(v_env_1785_);
lean_dec(v___x_1784_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1822_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v___f_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1800_; 
v___f_1796_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_1796_, 0, v_a_1780_);
v___x_1797_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1764_, v_env_1785_, v___f_1796_);
v___x_1798_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 5, v___x_1798_);
lean_ctor_set(v___x_1794_, 0, v___x_1797_);
v___x_1800_ = v___x_1794_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1797_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_nextMacroScope_1786_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v_ngen_1787_);
lean_ctor_set(v_reuseFailAlloc_1821_, 3, v_auxDeclNGen_1788_);
lean_ctor_set(v_reuseFailAlloc_1821_, 4, v_traceState_1789_);
lean_ctor_set(v_reuseFailAlloc_1821_, 5, v___x_1798_);
lean_ctor_set(v_reuseFailAlloc_1821_, 6, v_messages_1790_);
lean_ctor_set(v_reuseFailAlloc_1821_, 7, v_infoState_1791_);
lean_ctor_set(v_reuseFailAlloc_1821_, 8, v_snapshotTasks_1792_);
v___x_1800_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v_mctx_1803_; lean_object* v_zetaDeltaFVarIds_1804_; lean_object* v_postponed_1805_; lean_object* v_diag_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1819_; 
v___x_1801_ = lean_st_ref_set(v_a_1769_, v___x_1800_);
v___x_1802_ = lean_st_ref_take(v_a_1767_);
v_mctx_1803_ = lean_ctor_get(v___x_1802_, 0);
v_zetaDeltaFVarIds_1804_ = lean_ctor_get(v___x_1802_, 2);
v_postponed_1805_ = lean_ctor_get(v___x_1802_, 3);
v_diag_1806_ = lean_ctor_get(v___x_1802_, 4);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1819_ == 0)
{
lean_object* v_unused_1820_; 
v_unused_1820_ = lean_ctor_get(v___x_1802_, 1);
lean_dec(v_unused_1820_);
v___x_1808_ = v___x_1802_;
v_isShared_1809_ = v_isSharedCheck_1819_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_diag_1806_);
lean_inc(v_postponed_1805_);
lean_inc(v_zetaDeltaFVarIds_1804_);
lean_inc(v_mctx_1803_);
lean_dec(v___x_1802_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1819_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1812_; 
v___x_1810_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 1, v___x_1810_);
v___x_1812_ = v___x_1808_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_mctx_1803_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1810_);
lean_ctor_set(v_reuseFailAlloc_1818_, 2, v_zetaDeltaFVarIds_1804_);
lean_ctor_set(v_reuseFailAlloc_1818_, 3, v_postponed_1805_);
lean_ctor_set(v_reuseFailAlloc_1818_, 4, v_diag_1806_);
v___x_1812_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1813_ = lean_st_ref_set(v_a_1767_, v___x_1812_);
v___x_1814_ = lean_box(0);
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 0, v___x_1814_);
v___x_1816_ = v___x_1782_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1832_; 
lean_dec_ref(v_ext_1764_);
v_a_1825_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1827_ = v___x_1779_;
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_a_1825_);
lean_dec(v___x_1779_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1832_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v___x_1830_; 
if (v_isShared_1828_ == 0)
{
v___x_1830_ = v___x_1827_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1825_);
v___x_1830_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
return v___x_1830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_1833_, lean_object* v_declName_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_1833_, v_declName_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_1841_, lean_object* v_s_1842_){
_start:
{
lean_object* v_casesTypes_1843_; lean_object* v_extThms_1844_; lean_object* v_funCC_1845_; lean_object* v_ematch_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
v_casesTypes_1843_ = lean_ctor_get(v_s_1842_, 0);
v_extThms_1844_ = lean_ctor_get(v_s_1842_, 1);
v_funCC_1845_ = lean_ctor_get(v_s_1842_, 2);
v_ematch_1846_ = lean_ctor_get(v_s_1842_, 3);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_s_1842_);
if (v_isSharedCheck_1853_ == 0)
{
lean_object* v_unused_1854_; 
v_unused_1854_ = lean_ctor_get(v_s_1842_, 4);
lean_dec(v_unused_1854_);
v___x_1848_ = v_s_1842_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_ematch_1846_);
lean_inc(v_funCC_1845_);
lean_inc(v_extThms_1844_);
lean_inc(v_casesTypes_1843_);
lean_dec(v_s_1842_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 4, v_a_1841_);
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_casesTypes_1843_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_extThms_1844_);
lean_ctor_set(v_reuseFailAlloc_1852_, 2, v_funCC_1845_);
lean_ctor_set(v_reuseFailAlloc_1852_, 3, v_ematch_1846_);
lean_ctor_set(v_reuseFailAlloc_1852_, 4, v_a_1841_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_1855_, lean_object* v_declName_1856_, lean_object* v_a_1857_, lean_object* v_a_1858_, lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v___x_1862_; lean_object* v_ext_1863_; lean_object* v_toEnvExtension_1864_; lean_object* v_env_1865_; lean_object* v_asyncMode_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v_inj_1869_; lean_object* v___x_1870_; 
v___x_1862_ = lean_st_ref_get(v_a_1860_);
v_ext_1863_ = lean_ctor_get(v_ext_1855_, 1);
v_toEnvExtension_1864_ = lean_ctor_get(v_ext_1863_, 0);
v_env_1865_ = lean_ctor_get(v___x_1862_, 0);
lean_inc_ref(v_env_1865_);
lean_dec(v___x_1862_);
v_asyncMode_1866_ = lean_ctor_get(v_toEnvExtension_1864_, 2);
v___x_1867_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1868_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1867_, v_ext_1855_, v_env_1865_, v_asyncMode_1866_);
v_inj_1869_ = lean_ctor_get(v___x_1868_, 4);
lean_inc_ref(v_inj_1869_);
lean_dec(v___x_1868_);
v___x_1870_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_1869_, v_declName_1856_, v_a_1857_, v_a_1858_, v_a_1859_, v_a_1860_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1915_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1873_ = v___x_1870_;
v_isShared_1874_ = v_isSharedCheck_1915_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_a_1871_);
lean_dec(v___x_1870_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1915_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
lean_object* v___x_1875_; lean_object* v_env_1876_; lean_object* v_nextMacroScope_1877_; lean_object* v_ngen_1878_; lean_object* v_auxDeclNGen_1879_; lean_object* v_traceState_1880_; lean_object* v_messages_1881_; lean_object* v_infoState_1882_; lean_object* v_snapshotTasks_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1913_; 
v___x_1875_ = lean_st_ref_take(v_a_1860_);
v_env_1876_ = lean_ctor_get(v___x_1875_, 0);
v_nextMacroScope_1877_ = lean_ctor_get(v___x_1875_, 1);
v_ngen_1878_ = lean_ctor_get(v___x_1875_, 2);
v_auxDeclNGen_1879_ = lean_ctor_get(v___x_1875_, 3);
v_traceState_1880_ = lean_ctor_get(v___x_1875_, 4);
v_messages_1881_ = lean_ctor_get(v___x_1875_, 6);
v_infoState_1882_ = lean_ctor_get(v___x_1875_, 7);
v_snapshotTasks_1883_ = lean_ctor_get(v___x_1875_, 8);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1913_ == 0)
{
lean_object* v_unused_1914_; 
v_unused_1914_ = lean_ctor_get(v___x_1875_, 5);
lean_dec(v_unused_1914_);
v___x_1885_ = v___x_1875_;
v_isShared_1886_ = v_isSharedCheck_1913_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_snapshotTasks_1883_);
lean_inc(v_infoState_1882_);
lean_inc(v_messages_1881_);
lean_inc(v_traceState_1880_);
lean_inc(v_auxDeclNGen_1879_);
lean_inc(v_ngen_1878_);
lean_inc(v_nextMacroScope_1877_);
lean_inc(v_env_1876_);
lean_dec(v___x_1875_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1913_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___f_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
v___f_1887_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_1887_, 0, v_a_1871_);
v___x_1888_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1855_, v_env_1876_, v___f_1887_);
v___x_1889_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 5, v___x_1889_);
lean_ctor_set(v___x_1885_, 0, v___x_1888_);
v___x_1891_ = v___x_1885_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_nextMacroScope_1877_);
lean_ctor_set(v_reuseFailAlloc_1912_, 2, v_ngen_1878_);
lean_ctor_set(v_reuseFailAlloc_1912_, 3, v_auxDeclNGen_1879_);
lean_ctor_set(v_reuseFailAlloc_1912_, 4, v_traceState_1880_);
lean_ctor_set(v_reuseFailAlloc_1912_, 5, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1912_, 6, v_messages_1881_);
lean_ctor_set(v_reuseFailAlloc_1912_, 7, v_infoState_1882_);
lean_ctor_set(v_reuseFailAlloc_1912_, 8, v_snapshotTasks_1883_);
v___x_1891_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v_mctx_1894_; lean_object* v_zetaDeltaFVarIds_1895_; lean_object* v_postponed_1896_; lean_object* v_diag_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1910_; 
v___x_1892_ = lean_st_ref_set(v_a_1860_, v___x_1891_);
v___x_1893_ = lean_st_ref_take(v_a_1858_);
v_mctx_1894_ = lean_ctor_get(v___x_1893_, 0);
v_zetaDeltaFVarIds_1895_ = lean_ctor_get(v___x_1893_, 2);
v_postponed_1896_ = lean_ctor_get(v___x_1893_, 3);
v_diag_1897_ = lean_ctor_get(v___x_1893_, 4);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1893_);
if (v_isSharedCheck_1910_ == 0)
{
lean_object* v_unused_1911_; 
v_unused_1911_ = lean_ctor_get(v___x_1893_, 1);
lean_dec(v_unused_1911_);
v___x_1899_ = v___x_1893_;
v_isShared_1900_ = v_isSharedCheck_1910_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_diag_1897_);
lean_inc(v_postponed_1896_);
lean_inc(v_zetaDeltaFVarIds_1895_);
lean_inc(v_mctx_1894_);
lean_dec(v___x_1893_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1910_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v___x_1901_);
v___x_1903_ = v___x_1899_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_mctx_1894_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v___x_1901_);
lean_ctor_set(v_reuseFailAlloc_1909_, 2, v_zetaDeltaFVarIds_1895_);
lean_ctor_set(v_reuseFailAlloc_1909_, 3, v_postponed_1896_);
lean_ctor_set(v_reuseFailAlloc_1909_, 4, v_diag_1897_);
v___x_1903_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1904_ = lean_st_ref_set(v_a_1858_, v___x_1903_);
v___x_1905_ = lean_box(0);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1905_);
v___x_1907_ = v___x_1873_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1923_; 
lean_dec_ref(v_ext_1855_);
v_a_1916_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1923_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1918_ = v___x_1870_;
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_a_1916_);
lean_dec(v___x_1870_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1923_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1921_; 
if (v_isShared_1919_ == 0)
{
v___x_1921_ = v___x_1918_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1916_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object* v_ext_1924_, lean_object* v_declName_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_1924_, v_declName_1925_, v_a_1926_, v_a_1927_, v_a_1928_, v_a_1929_);
lean_dec(v_a_1929_);
lean_dec_ref(v_a_1928_);
lean_dec(v_a_1927_);
lean_dec_ref(v_a_1926_);
return v_res_1931_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1932_, lean_object* v_i_1933_, lean_object* v_k_1934_){
_start:
{
lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1935_ = lean_array_get_size(v_keys_1932_);
v___x_1936_ = lean_nat_dec_lt(v_i_1933_, v___x_1935_);
if (v___x_1936_ == 0)
{
lean_dec(v_i_1933_);
return v___x_1936_;
}
else
{
lean_object* v_k_x27_1937_; uint8_t v___x_1938_; 
v_k_x27_1937_ = lean_array_fget_borrowed(v_keys_1932_, v_i_1933_);
v___x_1938_ = lean_name_eq(v_k_1934_, v_k_x27_1937_);
if (v___x_1938_ == 0)
{
lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1939_ = lean_unsigned_to_nat(1u);
v___x_1940_ = lean_nat_add(v_i_1933_, v___x_1939_);
lean_dec(v_i_1933_);
v_i_1933_ = v___x_1940_;
goto _start;
}
else
{
lean_dec(v_i_1933_);
return v___x_1938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1942_, lean_object* v_i_1943_, lean_object* v_k_1944_){
_start:
{
uint8_t v_res_1945_; lean_object* v_r_1946_; 
v_res_1945_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_1942_, v_i_1943_, v_k_1944_);
lean_dec(v_k_1944_);
lean_dec_ref(v_keys_1942_);
v_r_1946_ = lean_box(v_res_1945_);
return v_r_1946_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1947_; size_t v___x_1948_; size_t v___x_1949_; 
v___x_1947_ = ((size_t)5ULL);
v___x_1948_ = ((size_t)1ULL);
v___x_1949_ = lean_usize_shift_left(v___x_1948_, v___x_1947_);
return v___x_1949_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1950_; size_t v___x_1951_; size_t v___x_1952_; 
v___x_1950_ = ((size_t)1ULL);
v___x_1951_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__0);
v___x_1952_ = lean_usize_sub(v___x_1951_, v___x_1950_);
return v___x_1952_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_1953_, size_t v_x_1954_, lean_object* v_x_1955_){
_start:
{
if (lean_obj_tag(v_x_1953_) == 0)
{
lean_object* v_es_1956_; lean_object* v___x_1957_; size_t v___x_1958_; size_t v___x_1959_; size_t v___x_1960_; lean_object* v_j_1961_; lean_object* v___x_1962_; 
v_es_1956_ = lean_ctor_get(v_x_1953_, 0);
v___x_1957_ = lean_box(2);
v___x_1958_ = ((size_t)5ULL);
v___x_1959_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1);
v___x_1960_ = lean_usize_land(v_x_1954_, v___x_1959_);
v_j_1961_ = lean_usize_to_nat(v___x_1960_);
v___x_1962_ = lean_array_get_borrowed(v___x_1957_, v_es_1956_, v_j_1961_);
lean_dec(v_j_1961_);
switch(lean_obj_tag(v___x_1962_))
{
case 0:
{
lean_object* v_key_1963_; uint8_t v___x_1964_; 
v_key_1963_ = lean_ctor_get(v___x_1962_, 0);
v___x_1964_ = lean_name_eq(v_x_1955_, v_key_1963_);
return v___x_1964_;
}
case 1:
{
lean_object* v_node_1965_; size_t v___x_1966_; 
v_node_1965_ = lean_ctor_get(v___x_1962_, 0);
v___x_1966_ = lean_usize_shift_right(v_x_1954_, v___x_1958_);
v_x_1953_ = v_node_1965_;
v_x_1954_ = v___x_1966_;
goto _start;
}
default: 
{
uint8_t v___x_1968_; 
v___x_1968_ = 0;
return v___x_1968_;
}
}
}
else
{
lean_object* v_ks_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v_ks_1969_ = lean_ctor_get(v_x_1953_, 0);
v___x_1970_ = lean_unsigned_to_nat(0u);
v___x_1971_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_1969_, v___x_1970_, v_x_1955_);
return v___x_1971_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_1972_, lean_object* v_x_1973_, lean_object* v_x_1974_){
_start:
{
size_t v_x_343__boxed_1975_; uint8_t v_res_1976_; lean_object* v_r_1977_; 
v_x_343__boxed_1975_ = lean_unbox_usize(v_x_1973_);
lean_dec(v_x_1973_);
v_res_1976_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_1972_, v_x_343__boxed_1975_, v_x_1974_);
lean_dec(v_x_1974_);
lean_dec_ref(v_x_1972_);
v_r_1977_ = lean_box(v_res_1976_);
return v_r_1977_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1978_; uint64_t v___x_1979_; 
v___x_1978_ = lean_unsigned_to_nat(1723u);
v___x_1979_ = lean_uint64_of_nat(v___x_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_1980_, lean_object* v_x_1981_){
_start:
{
uint64_t v___y_1983_; 
if (lean_obj_tag(v_x_1981_) == 0)
{
uint64_t v___x_1986_; 
v___x_1986_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_1983_ = v___x_1986_;
goto v___jp_1982_;
}
else
{
uint64_t v_hash_1987_; 
v_hash_1987_ = lean_ctor_get_uint64(v_x_1981_, sizeof(void*)*2);
v___y_1983_ = v_hash_1987_;
goto v___jp_1982_;
}
v___jp_1982_:
{
size_t v___x_1984_; uint8_t v___x_1985_; 
v___x_1984_ = lean_uint64_to_usize(v___y_1983_);
v___x_1985_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_1980_, v___x_1984_, v_x_1981_);
return v___x_1985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_1988_, lean_object* v_x_1989_){
_start:
{
uint8_t v_res_1990_; lean_object* v_r_1991_; 
v_res_1990_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_1988_, v_x_1989_);
lean_dec(v_x_1989_);
lean_dec_ref(v_x_1988_);
v_r_1991_ = lean_box(v_res_1990_);
return v_r_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_1992_, lean_object* v_declName_1993_, lean_object* v_a_1994_){
_start:
{
lean_object* v___x_1996_; lean_object* v_ext_1997_; lean_object* v_toEnvExtension_1998_; lean_object* v_env_1999_; lean_object* v_asyncMode_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v_extThms_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v___x_1996_ = lean_st_ref_get(v_a_1994_);
v_ext_1997_ = lean_ctor_get(v_ext_1992_, 1);
v_toEnvExtension_1998_ = lean_ctor_get(v_ext_1997_, 0);
v_env_1999_ = lean_ctor_get(v___x_1996_, 0);
lean_inc_ref(v_env_1999_);
lean_dec(v___x_1996_);
v_asyncMode_2000_ = lean_ctor_get(v_toEnvExtension_1998_, 2);
v___x_2001_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2002_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2001_, v_ext_1992_, v_env_1999_, v_asyncMode_2000_);
v_extThms_2003_ = lean_ctor_get(v___x_2002_, 1);
lean_inc_ref(v_extThms_2003_);
lean_dec(v___x_2002_);
v___x_2004_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_2003_, v_declName_1993_);
lean_dec_ref(v_extThms_2003_);
v___x_2005_ = lean_box(v___x_2004_);
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_2007_, lean_object* v_declName_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2007_, v_declName_2008_, v_a_2009_);
lean_dec(v_a_2009_);
lean_dec(v_declName_2008_);
lean_dec_ref(v_ext_2007_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_2012_, lean_object* v_declName_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2012_, v_declName_2013_, v_a_2015_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_2018_, lean_object* v_declName_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_2018_, v_declName_2019_, v_a_2020_, v_a_2021_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec(v_declName_2019_);
lean_dec_ref(v_ext_2018_);
return v_res_2023_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_2024_, lean_object* v_x_2025_, lean_object* v_x_2026_){
_start:
{
uint8_t v___x_2027_; 
v___x_2027_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2025_, v_x_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_2028_, lean_object* v_x_2029_, lean_object* v_x_2030_){
_start:
{
uint8_t v_res_2031_; lean_object* v_r_2032_; 
v_res_2031_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_2028_, v_x_2029_, v_x_2030_);
lean_dec(v_x_2030_);
lean_dec_ref(v_x_2029_);
v_r_2032_ = lean_box(v_res_2031_);
return v_r_2032_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_2033_, lean_object* v_x_2034_, size_t v_x_2035_, lean_object* v_x_2036_){
_start:
{
uint8_t v___x_2037_; 
v___x_2037_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2034_, v_x_2035_, v_x_2036_);
return v___x_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2038_, lean_object* v_x_2039_, lean_object* v_x_2040_, lean_object* v_x_2041_){
_start:
{
size_t v_x_440__boxed_2042_; uint8_t v_res_2043_; lean_object* v_r_2044_; 
v_x_440__boxed_2042_ = lean_unbox_usize(v_x_2040_);
lean_dec(v_x_2040_);
v_res_2043_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_2038_, v_x_2039_, v_x_440__boxed_2042_, v_x_2041_);
lean_dec(v_x_2041_);
lean_dec_ref(v_x_2039_);
v_r_2044_ = lean_box(v_res_2043_);
return v_r_2044_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2045_, lean_object* v_keys_2046_, lean_object* v_vals_2047_, lean_object* v_heq_2048_, lean_object* v_i_2049_, lean_object* v_k_2050_){
_start:
{
uint8_t v___x_2051_; 
v___x_2051_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_2046_, v_i_2049_, v_k_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2052_, lean_object* v_keys_2053_, lean_object* v_vals_2054_, lean_object* v_heq_2055_, lean_object* v_i_2056_, lean_object* v_k_2057_){
_start:
{
uint8_t v_res_2058_; lean_object* v_r_2059_; 
v_res_2058_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_2052_, v_keys_2053_, v_vals_2054_, v_heq_2055_, v_i_2056_, v_k_2057_);
lean_dec(v_k_2057_);
lean_dec_ref(v_vals_2054_);
lean_dec_ref(v_keys_2053_);
v_r_2059_ = lean_box(v_res_2058_);
return v_r_2059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_2060_, lean_object* v_declName_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v___x_2064_; lean_object* v_ext_2065_; lean_object* v_toEnvExtension_2066_; lean_object* v_env_2067_; lean_object* v_asyncMode_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v_inj_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2064_ = lean_st_ref_get(v_a_2062_);
v_ext_2065_ = lean_ctor_get(v_ext_2060_, 1);
v_toEnvExtension_2066_ = lean_ctor_get(v_ext_2065_, 0);
v_env_2067_ = lean_ctor_get(v___x_2064_, 0);
lean_inc_ref(v_env_2067_);
lean_dec(v___x_2064_);
v_asyncMode_2068_ = lean_ctor_get(v_toEnvExtension_2066_, 2);
v___x_2069_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2070_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2069_, v_ext_2060_, v_env_2067_, v_asyncMode_2068_);
v_inj_2071_ = lean_ctor_get(v___x_2070_, 4);
lean_inc_ref(v_inj_2071_);
lean_dec(v___x_2070_);
v___x_2072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2072_, 0, v_declName_2061_);
v___x_2073_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_2071_, v___x_2072_);
lean_dec_ref(v___x_2072_);
lean_dec_ref(v_inj_2071_);
v___x_2074_ = lean_box(v___x_2073_);
v___x_2075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_2076_, lean_object* v_declName_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2076_, v_declName_2077_, v_a_2078_);
lean_dec(v_a_2078_);
lean_dec_ref(v_ext_2076_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_2081_, lean_object* v_declName_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2081_, v_declName_2082_, v_a_2084_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_2087_, lean_object* v_declName_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_2087_, v_declName_2088_, v_a_2089_, v_a_2090_);
lean_dec(v_a_2090_);
lean_dec_ref(v_a_2089_);
lean_dec_ref(v_ext_2087_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_2093_, lean_object* v_declName_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v___x_2097_; lean_object* v_ext_2098_; lean_object* v_toEnvExtension_2099_; lean_object* v_env_2100_; lean_object* v_asyncMode_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v_funCC_2104_; uint8_t v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2097_ = lean_st_ref_get(v_a_2095_);
v_ext_2098_ = lean_ctor_get(v_ext_2093_, 1);
v_toEnvExtension_2099_ = lean_ctor_get(v_ext_2098_, 0);
v_env_2100_ = lean_ctor_get(v___x_2097_, 0);
lean_inc_ref(v_env_2100_);
lean_dec(v___x_2097_);
v_asyncMode_2101_ = lean_ctor_get(v_toEnvExtension_2099_, 2);
v___x_2102_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2103_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2102_, v_ext_2093_, v_env_2100_, v_asyncMode_2101_);
v_funCC_2104_ = lean_ctor_get(v___x_2103_, 2);
lean_inc(v_funCC_2104_);
lean_dec(v___x_2103_);
v___x_2105_ = l_Lean_NameSet_contains(v_funCC_2104_, v_declName_2094_);
lean_dec(v_funCC_2104_);
v___x_2106_ = lean_box(v___x_2105_);
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_2108_, lean_object* v_declName_2109_, lean_object* v_a_2110_, lean_object* v_a_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2108_, v_declName_2109_, v_a_2110_);
lean_dec(v_a_2110_);
lean_dec(v_declName_2109_);
lean_dec_ref(v_ext_2108_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_2113_, lean_object* v_declName_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2113_, v_declName_2114_, v_a_2116_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_2119_, lean_object* v_declName_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_2119_, v_declName_2120_, v_a_2121_, v_a_2122_);
lean_dec(v_a_2122_);
lean_dec_ref(v_a_2121_);
lean_dec(v_declName_2120_);
lean_dec_ref(v_ext_2119_);
return v_res_2124_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_2149_ = l_Lean_mkAtom(v___x_2148_);
return v___x_2149_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2150_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_2151_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2152_ = lean_array_push(v___x_2151_, v___x_2150_);
return v___x_2152_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
v___x_2161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_2162_ = l_Lean_mkAtom(v___x_2161_);
return v___x_2162_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_2164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2165_ = lean_array_push(v___x_2164_, v___x_2163_);
return v___x_2165_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2166_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_2167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_2168_ = lean_box(2);
v___x_2169_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v___x_2167_);
lean_ctor_set(v___x_2169_, 2, v___x_2166_);
return v___x_2169_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_2171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_2172_ = lean_array_push(v___x_2171_, v___x_2170_);
return v___x_2172_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2173_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_2174_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_2175_ = lean_box(2);
v___x_2176_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
lean_ctor_set(v___x_2176_, 1, v___x_2174_);
lean_ctor_set(v___x_2176_, 2, v___x_2173_);
return v___x_2176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2177_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_2178_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2179_ = lean_array_push(v___x_2178_, v___x_2177_);
return v___x_2179_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2180_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_2181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_2182_ = lean_box(2);
v___x_2183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2183_, 0, v___x_2182_);
lean_ctor_set(v___x_2183_, 1, v___x_2181_);
lean_ctor_set(v___x_2183_, 2, v___x_2180_);
return v___x_2183_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v___x_2184_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_2185_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2186_ = lean_array_push(v___x_2185_, v___x_2184_);
return v___x_2186_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2187_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_2188_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_2189_ = lean_box(2);
v___x_2190_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2189_);
lean_ctor_set(v___x_2190_, 1, v___x_2188_);
lean_ctor_set(v___x_2190_, 2, v___x_2187_);
return v___x_2190_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2191_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_2192_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2193_ = lean_array_push(v___x_2192_, v___x_2191_);
return v___x_2193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2194_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_2195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_2196_ = lean_box(2);
v___x_2197_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2196_);
lean_ctor_set(v___x_2197_, 1, v___x_2195_);
lean_ctor_set(v___x_2197_, 2, v___x_2194_);
return v___x_2197_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_2198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_2199_, lean_object* v_ext_2200_, lean_object* v_____r_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
uint8_t v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = 0;
lean_inc(v_declName_2199_);
v___x_2208_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_2199_, v___x_2207_, v___y_2204_, v___y_2205_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; uint8_t v___x_2210_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref(v___x_2208_);
v___x_2210_ = lean_unbox(v_a_2209_);
lean_dec(v_a_2209_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; lean_object* v_a_2212_; uint8_t v___x_2213_; 
v___x_2211_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2200_, v_declName_2199_, v___y_2205_);
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
lean_dec_ref(v___x_2211_);
v___x_2213_ = lean_unbox(v_a_2212_);
lean_dec(v_a_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; lean_object* v_a_2215_; uint8_t v___x_2216_; 
lean_inc(v_declName_2199_);
v___x_2214_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2200_, v_declName_2199_, v___y_2205_);
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref(v___x_2214_);
v___x_2216_ = lean_unbox(v_a_2215_);
lean_dec(v_a_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v_a_2218_; uint8_t v___x_2219_; 
v___x_2217_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2200_, v_declName_2199_, v___y_2205_);
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref(v___x_2217_);
v___x_2219_ = lean_unbox(v_a_2218_);
lean_dec(v_a_2218_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; 
v___x_2220_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_2200_, v_declName_2199_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
return v___x_2220_;
}
else
{
lean_object* v___x_2221_; 
v___x_2221_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2200_, v_declName_2199_, v___y_2204_, v___y_2205_);
return v___x_2221_;
}
}
else
{
lean_object* v___x_2222_; 
v___x_2222_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_2200_, v_declName_2199_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
return v___x_2222_;
}
}
else
{
lean_object* v___x_2223_; 
v___x_2223_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2200_, v_declName_2199_, v___y_2204_, v___y_2205_);
return v___x_2223_;
}
}
else
{
lean_object* v___x_2224_; 
v___x_2224_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2200_, v_declName_2199_, v___y_2204_, v___y_2205_);
return v___x_2224_;
}
}
else
{
lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec_ref(v_ext_2200_);
lean_dec(v_declName_2199_);
v_a_2225_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2208_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2208_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_2233_, lean_object* v_ext_2234_, lean_object* v_____r_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2233_, v_ext_2234_, v_____r_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object* v_msgData_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; lean_object* v_env_2249_; lean_object* v___x_2250_; lean_object* v_mctx_2251_; lean_object* v_lctx_2252_; lean_object* v_options_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2248_ = lean_st_ref_get(v___y_2246_);
v_env_2249_ = lean_ctor_get(v___x_2248_, 0);
lean_inc_ref(v_env_2249_);
lean_dec(v___x_2248_);
v___x_2250_ = lean_st_ref_get(v___y_2244_);
v_mctx_2251_ = lean_ctor_get(v___x_2250_, 0);
lean_inc_ref(v_mctx_2251_);
lean_dec(v___x_2250_);
v_lctx_2252_ = lean_ctor_get(v___y_2243_, 2);
v_options_2253_ = lean_ctor_get(v___y_2245_, 2);
lean_inc_ref(v_options_2253_);
lean_inc_ref(v_lctx_2252_);
v___x_2254_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2254_, 0, v_env_2249_);
lean_ctor_set(v___x_2254_, 1, v_mctx_2251_);
lean_ctor_set(v___x_2254_, 2, v_lctx_2252_);
lean_ctor_set(v___x_2254_, 3, v_options_2253_);
v___x_2255_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set(v___x_2255_, 1, v_msgData_2242_);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object* v_msgData_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msgData_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_ref_2270_; lean_object* v___x_2271_; lean_object* v_a_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2280_; 
v_ref_2270_ = lean_ctor_get(v___y_2267_, 5);
v___x_2271_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2274_ = v___x_2271_;
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_a_2272_);
lean_dec(v___x_2271_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2280_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2278_; 
lean_inc(v_ref_2270_);
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v_ref_2270_);
lean_ctor_set(v___x_2276_, 1, v_a_2272_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set_tag(v___x_2274_, 1);
lean_ctor_set(v___x_2274_, 0, v___x_2276_);
v___x_2278_ = v___x_2274_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
lean_dec(v___y_2285_);
lean_dec_ref(v___y_2284_);
lean_dec(v___y_2283_);
lean_dec_ref(v___y_2282_);
return v_res_2287_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2294_; uint64_t v___x_2295_; 
v___x_2294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2295_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2294_);
return v___x_2295_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2296_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_2297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2298_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set_uint64(v___x_2298_, sizeof(void*)*1, v___x_2296_);
return v___x_2298_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2299_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
return v___x_2301_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2302_ = lean_box(1);
v___x_2303_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2304_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
lean_ctor_set(v___x_2305_, 1, v___x_2303_);
lean_ctor_set(v___x_2305_, 2, v___x_2302_);
return v___x_2305_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2309_ = lean_unsigned_to_nat(0u);
v___x_2310_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v___x_2309_);
lean_ctor_set(v___x_2310_, 2, v___x_2309_);
lean_ctor_set(v___x_2310_, 3, v___x_2309_);
lean_ctor_set(v___x_2310_, 4, v___x_2308_);
lean_ctor_set(v___x_2310_, 5, v___x_2308_);
lean_ctor_set(v___x_2310_, 6, v___x_2308_);
lean_ctor_set(v___x_2310_, 7, v___x_2308_);
lean_ctor_set(v___x_2310_, 8, v___x_2308_);
lean_ctor_set(v___x_2310_, 9, v___x_2308_);
return v___x_2310_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2312_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
lean_ctor_set(v___x_2312_, 2, v___x_2311_);
lean_ctor_set(v___x_2312_, 3, v___x_2311_);
lean_ctor_set(v___x_2312_, 4, v___x_2311_);
lean_ctor_set(v___x_2312_, 5, v___x_2311_);
return v___x_2312_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
lean_ctor_set(v___x_2314_, 2, v___x_2313_);
lean_ctor_set(v___x_2314_, 3, v___x_2313_);
lean_ctor_set(v___x_2314_, 4, v___x_2313_);
return v___x_2314_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10));
v___x_2317_ = l_Lean_stringToMessageData(v___x_2316_);
return v___x_2317_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12));
v___x_2320_ = l_Lean_stringToMessageData(v___x_2319_);
return v___x_2320_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14));
v___x_2323_ = l_Lean_stringToMessageData(v___x_2322_);
return v___x_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v___x_2324_, lean_object* v_ext_2325_, uint8_t v_showInfo_2326_, lean_object* v_attrName_2327_, lean_object* v_declName_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
uint8_t v___x_2332_; uint8_t v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___y_2347_; 
v___x_2332_ = 1;
v___x_2333_ = 0;
v___x_2334_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_2335_ = lean_unsigned_to_nat(0u);
v___x_2336_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2337_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_2338_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6));
v___x_2339_ = lean_box(0);
lean_inc(v___x_2324_);
v___x_2340_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2340_, 0, v___x_2334_);
lean_ctor_set(v___x_2340_, 1, v___x_2324_);
lean_ctor_set(v___x_2340_, 2, v___x_2337_);
lean_ctor_set(v___x_2340_, 3, v___x_2338_);
lean_ctor_set(v___x_2340_, 4, v___x_2339_);
lean_ctor_set(v___x_2340_, 5, v___x_2335_);
lean_ctor_set(v___x_2340_, 6, v___x_2339_);
lean_ctor_set_uint8(v___x_2340_, sizeof(void*)*7, v___x_2333_);
lean_ctor_set_uint8(v___x_2340_, sizeof(void*)*7 + 1, v___x_2333_);
lean_ctor_set_uint8(v___x_2340_, sizeof(void*)*7 + 2, v___x_2333_);
lean_ctor_set_uint8(v___x_2340_, sizeof(void*)*7 + 3, v___x_2332_);
v___x_2341_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_2342_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_2343_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_2344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2341_);
lean_ctor_set(v___x_2344_, 1, v___x_2342_);
lean_ctor_set(v___x_2344_, 2, v___x_2324_);
lean_ctor_set(v___x_2344_, 3, v___x_2336_);
lean_ctor_set(v___x_2344_, 4, v___x_2343_);
v___x_2345_ = lean_st_mk_ref(v___x_2344_);
if (v_showInfo_2326_ == 0)
{
lean_object* v___x_2357_; lean_object* v___x_2358_; 
lean_dec(v_attrName_2327_);
v___x_2357_ = lean_box(0);
v___x_2358_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2328_, v_ext_2325_, v___x_2357_, v___x_2340_, v___x_2345_, v___y_2329_, v___y_2330_);
lean_dec_ref(v___x_2340_);
v___y_2347_ = v___x_2358_;
goto v___jp_2346_;
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_dec(v_declName_2328_);
lean_dec_ref(v_ext_2325_);
v___x_2359_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11);
v___x_2360_ = l_Lean_MessageData_ofName(v_attrName_2327_);
lean_inc_ref(v___x_2360_);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13);
v___x_2363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2361_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
v___x_2364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2364_, 0, v___x_2363_);
lean_ctor_set(v___x_2364_, 1, v___x_2360_);
v___x_2365_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15);
v___x_2366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2364_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2366_, v___x_2340_, v___x_2345_, v___y_2329_, v___y_2330_);
lean_dec_ref(v___x_2340_);
v___y_2347_ = v___x_2367_;
goto v___jp_2346_;
}
v___jp_2346_:
{
if (lean_obj_tag(v___y_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2356_; 
v_a_2348_ = lean_ctor_get(v___y_2347_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___y_2347_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2350_ = v___y_2347_;
v_isShared_2351_ = v_isSharedCheck_2356_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___y_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2356_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2352_ = lean_st_ref_get(v___x_2345_);
lean_dec(v___x_2345_);
lean_dec(v___x_2352_);
if (v_isShared_2351_ == 0)
{
v___x_2354_ = v___x_2350_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2348_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
else
{
lean_dec(v___x_2345_);
return v___y_2347_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v___x_2368_, lean_object* v_ext_2369_, lean_object* v_showInfo_2370_, lean_object* v_attrName_2371_, lean_object* v_declName_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
uint8_t v_showInfo_boxed_2376_; lean_object* v_res_2377_; 
v_showInfo_boxed_2376_ = lean_unbox(v_showInfo_2370_);
v_res_2377_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v___x_2368_, v_ext_2369_, v_showInfo_boxed_2376_, v_attrName_2371_, v_declName_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_2380_, uint8_t v_attrKind_2381_, uint8_t v_showInfo_2382_, uint8_t v_minIndexable_2383_, lean_object* v_as_x27_2384_, lean_object* v_b_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
if (lean_obj_tag(v_as_x27_2384_) == 0)
{
lean_object* v___x_2391_; 
lean_dec_ref(v_ext_2380_);
v___x_2391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2391_, 0, v_b_2385_);
return v___x_2391_;
}
else
{
lean_object* v_head_2392_; lean_object* v_tail_2393_; lean_object* v___x_2394_; 
v_head_2392_ = lean_ctor_get(v_as_x27_2384_, 0);
lean_inc(v_head_2392_);
v_tail_2393_ = lean_ctor_get(v_as_x27_2384_, 1);
lean_inc(v_tail_2393_);
lean_dec_ref(v_as_x27_2384_);
v___x_2394_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2389_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref(v___x_2394_);
v___x_2396_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc_ref(v_ext_2380_);
v___x_2397_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2380_, v_head_2392_, v_attrKind_2381_, v___x_2396_, v_a_2395_, v_showInfo_2382_, v_minIndexable_2383_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v___x_2398_; 
lean_dec_ref(v___x_2397_);
v___x_2398_ = lean_box(0);
v_as_x27_2384_ = v_tail_2393_;
v_b_2385_ = v___x_2398_;
goto _start;
}
else
{
lean_dec(v_tail_2393_);
lean_dec_ref(v_ext_2380_);
return v___x_2397_;
}
}
else
{
lean_object* v_a_2400_; lean_object* v___x_2402_; uint8_t v_isShared_2403_; uint8_t v_isSharedCheck_2407_; 
lean_dec(v_tail_2393_);
lean_dec(v_head_2392_);
lean_dec_ref(v_ext_2380_);
v_a_2400_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2407_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2407_ == 0)
{
v___x_2402_ = v___x_2394_;
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
else
{
lean_inc(v_a_2400_);
lean_dec(v___x_2394_);
v___x_2402_ = lean_box(0);
v_isShared_2403_ = v_isSharedCheck_2407_;
goto v_resetjp_2401_;
}
v_resetjp_2401_:
{
lean_object* v___x_2405_; 
if (v_isShared_2403_ == 0)
{
v___x_2405_ = v___x_2402_;
goto v_reusejp_2404_;
}
else
{
lean_object* v_reuseFailAlloc_2406_; 
v_reuseFailAlloc_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
v___x_2405_ = v_reuseFailAlloc_2406_;
goto v_reusejp_2404_;
}
v_reusejp_2404_:
{
return v___x_2405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_2408_, lean_object* v_attrKind_2409_, lean_object* v_showInfo_2410_, lean_object* v_minIndexable_2411_, lean_object* v_as_x27_2412_, lean_object* v_b_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
uint8_t v_attrKind_boxed_2419_; uint8_t v_showInfo_boxed_2420_; uint8_t v_minIndexable_boxed_2421_; lean_object* v_res_2422_; 
v_attrKind_boxed_2419_ = lean_unbox(v_attrKind_2409_);
v_showInfo_boxed_2420_ = lean_unbox(v_showInfo_2410_);
v_minIndexable_boxed_2421_ = lean_unbox(v_minIndexable_2411_);
v_res_2422_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2408_, v_attrKind_boxed_2419_, v_showInfo_boxed_2420_, v_minIndexable_boxed_2421_, v_as_x27_2412_, v_b_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
return v_res_2422_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_2425_ = l_Lean_stringToMessageData(v___x_2424_);
return v___x_2425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_2428_ = l_Lean_stringToMessageData(v___x_2427_);
return v___x_2428_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_2431_ = l_Lean_stringToMessageData(v___x_2430_);
return v___x_2431_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_2434_ = l_Lean_stringToMessageData(v___x_2433_);
return v___x_2434_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10));
v___x_2440_ = l_Lean_stringToMessageData(v___x_2439_);
return v___x_2440_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12));
v___x_2443_ = l_Lean_stringToMessageData(v___x_2442_);
return v___x_2443_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14));
v___x_2446_ = l_Lean_stringToMessageData(v___x_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_stx_2447_, lean_object* v_ext_2448_, lean_object* v_declName_2449_, uint8_t v_attrKind_2450_, uint8_t v_showInfo_2451_, uint8_t v_minIndexable_2452_, uint8_t v___x_2453_, lean_object* v_attrName_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v___y_2461_; lean_object* v___y_2462_; lean_object* v___y_2463_; lean_object* v___y_2464_; lean_object* v___x_2488_; 
v___x_2488_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_2447_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_a_2489_; 
v_a_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_a_2489_);
lean_dec_ref(v___x_2488_);
switch(lean_obj_tag(v_a_2489_))
{
case 0:
{
lean_object* v_k_2490_; 
lean_dec(v_attrName_2454_);
lean_dec(v_stx_2447_);
v_k_2490_ = lean_ctor_get(v_a_2489_, 0);
lean_inc(v_k_2490_);
lean_dec_ref(v_a_2489_);
if (lean_obj_tag(v_k_2490_) == 9)
{
lean_object* v___x_2491_; 
lean_dec(v_declName_2449_);
lean_dec_ref(v_ext_2448_);
v___x_2491_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_2457_, v___y_2458_);
return v___x_2491_;
}
else
{
lean_object* v___x_2492_; 
v___x_2492_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2458_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2494_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref(v___x_2492_);
v___x_2494_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2448_, v_declName_2449_, v_attrKind_2450_, v_k_2490_, v_a_2493_, v_showInfo_2451_, v_minIndexable_2452_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2494_;
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec(v_k_2490_);
lean_dec(v_declName_2449_);
lean_dec_ref(v_ext_2448_);
v_a_2495_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2492_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2492_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
case 1:
{
uint8_t v_eager_2503_; lean_object* v___x_2504_; 
lean_dec(v_attrName_2454_);
lean_dec(v_stx_2447_);
v_eager_2503_ = lean_ctor_get_uint8(v_a_2489_, 0);
lean_dec_ref(v_a_2489_);
v___x_2504_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2448_, v_declName_2449_, v_eager_2503_, v_attrKind_2450_, v___y_2457_, v___y_2458_);
return v___x_2504_;
}
case 2:
{
lean_object* v___x_2505_; 
lean_dec(v_stx_2447_);
lean_inc(v_declName_2449_);
v___x_2505_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_2449_, v___x_2453_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v_a_2506_; 
v_a_2506_ = lean_ctor_get(v___x_2505_, 0);
lean_inc(v_a_2506_);
lean_dec_ref(v___x_2505_);
if (lean_obj_tag(v_a_2506_) == 1)
{
lean_object* v_val_2507_; lean_object* v_ctors_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_dec(v_attrName_2454_);
lean_dec(v_declName_2449_);
v_val_2507_ = lean_ctor_get(v_a_2506_, 0);
lean_inc(v_val_2507_);
lean_dec_ref(v_a_2506_);
v_ctors_2508_ = lean_ctor_get(v_val_2507_, 4);
lean_inc(v_ctors_2508_);
lean_dec(v_val_2507_);
v___x_2509_ = lean_box(0);
v___x_2510_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2448_, v_attrKind_2450_, v_showInfo_2451_, v_minIndexable_2452_, v_ctors_2508_, v___x_2509_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2517_ == 0)
{
lean_object* v_unused_2518_; 
v_unused_2518_ = lean_ctor_get(v___x_2510_, 0);
lean_dec(v_unused_2518_);
v___x_2512_ = v___x_2510_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_dec(v___x_2510_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 0, v___x_2509_);
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v___x_2509_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
else
{
return v___x_2510_;
}
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
lean_dec(v_a_2506_);
lean_dec_ref(v_ext_2448_);
v___x_2519_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3);
v___x_2520_ = l_Lean_MessageData_ofName(v_attrName_2454_);
v___x_2521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_2523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2521_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = l_Lean_MessageData_ofConstName(v_declName_2449_, v___x_2453_);
v___x_2525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2523_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
v___x_2526_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2527_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2528_;
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_dec(v_attrName_2454_);
lean_dec(v_declName_2449_);
lean_dec_ref(v_ext_2448_);
v_a_2529_ = lean_ctor_get(v___x_2505_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2505_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2505_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
case 3:
{
lean_object* v___x_2537_; 
lean_dec(v_attrName_2454_);
lean_inc(v_declName_2449_);
v___x_2537_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_2449_, v___x_2453_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v_a_2538_; 
v_a_2538_ = lean_ctor_get(v___x_2537_, 0);
lean_inc(v_a_2538_);
lean_dec_ref(v___x_2537_);
if (lean_obj_tag(v_a_2538_) == 1)
{
lean_object* v_val_2539_; lean_object* v___x_2540_; 
lean_dec(v_declName_2449_);
lean_dec(v_stx_2447_);
v_val_2539_ = lean_ctor_get(v_a_2538_, 0);
lean_inc_n(v_val_2539_, 2);
lean_dec_ref(v_a_2538_);
lean_inc_ref(v_ext_2448_);
v___x_2540_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2448_, v_val_2539_, v___x_2453_, v_attrKind_2450_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v___x_2541_; 
lean_dec_ref(v___x_2540_);
v___x_2541_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_2539_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2562_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2562_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2562_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
if (lean_obj_tag(v_a_2542_) == 1)
{
lean_object* v_val_2546_; lean_object* v_ctors_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
lean_del_object(v___x_2544_);
v_val_2546_ = lean_ctor_get(v_a_2542_, 0);
lean_inc(v_val_2546_);
lean_dec_ref(v_a_2542_);
v_ctors_2547_ = lean_ctor_get(v_val_2546_, 4);
lean_inc(v_ctors_2547_);
lean_dec(v_val_2546_);
v___x_2548_ = lean_box(0);
v___x_2549_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2448_, v_attrKind_2450_, v_showInfo_2451_, v_minIndexable_2452_, v_ctors_2547_, v___x_2548_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2556_ == 0)
{
lean_object* v_unused_2557_; 
v_unused_2557_ = lean_ctor_get(v___x_2549_, 0);
lean_dec(v_unused_2557_);
v___x_2551_ = v___x_2549_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_dec(v___x_2549_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v___x_2548_);
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2548_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
else
{
return v___x_2549_;
}
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2560_; 
lean_dec(v_a_2542_);
lean_dec_ref(v_ext_2448_);
v___x_2558_ = lean_box(0);
if (v_isShared_2545_ == 0)
{
lean_ctor_set(v___x_2544_, 0, v___x_2558_);
v___x_2560_ = v___x_2544_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec_ref(v_ext_2448_);
v_a_2563_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2541_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2541_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
else
{
lean_dec(v_val_2539_);
lean_dec_ref(v_ext_2448_);
return v___x_2540_;
}
}
else
{
lean_object* v___x_2571_; 
lean_dec(v_a_2538_);
v___x_2571_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2458_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2573_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref(v___x_2571_);
v___x_2573_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_2448_, v_stx_2447_, v_declName_2449_, v_attrKind_2450_, v_a_2572_, v_minIndexable_2452_, v_showInfo_2451_, v___x_2453_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2573_;
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec(v_declName_2449_);
lean_dec_ref(v_ext_2448_);
lean_dec(v_stx_2447_);
v_a_2574_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2571_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2571_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_dec(v_declName_2449_);
lean_dec_ref(v_ext_2448_);
lean_dec(v_stx_2447_);
v_a_2582_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2537_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2537_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
case 4:
{
lean_object* v___x_2590_; 
lean_dec(v_attrName_2454_);
lean_dec(v_stx_2447_);
v___x_2590_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2448_, v_declName_2449_, v_attrKind_2450_, v___y_2457_, v___y_2458_);
return v___x_2590_;
}
case 5:
{
lean_object* v_prio_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
lean_dec_ref(v_ext_2448_);
lean_dec(v_stx_2447_);
v_prio_2591_ = lean_ctor_get(v_a_2489_, 0);
lean_inc(v_prio_2591_);
lean_dec_ref(v_a_2489_);
v___x_2592_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2593_ = lean_name_eq(v_attrName_2454_, v___x_2592_);
lean_dec(v_attrName_2454_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
lean_dec(v_prio_2591_);
lean_dec(v_declName_2449_);
v___x_2594_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11);
v___x_2595_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2594_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2595_;
}
else
{
lean_object* v___x_2596_; 
v___x_2596_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_2449_, v_attrKind_2450_, v_prio_2591_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2596_;
}
}
case 6:
{
lean_object* v___x_2597_; 
lean_dec(v_attrName_2454_);
lean_dec(v_stx_2447_);
v___x_2597_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_2448_, v_declName_2449_, v_attrKind_2450_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2597_;
}
case 7:
{
lean_object* v___x_2598_; 
lean_dec(v_attrName_2454_);
lean_dec(v_stx_2447_);
v___x_2598_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2448_, v_declName_2449_, v_attrKind_2450_, v___y_2457_, v___y_2458_);
return v___x_2598_;
}
case 8:
{
uint8_t v_post_2599_; uint8_t v_inv_2600_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___x_2609_; uint8_t v___x_2610_; 
lean_dec_ref(v_ext_2448_);
lean_dec(v_stx_2447_);
v_post_2599_ = lean_ctor_get_uint8(v_a_2489_, 0);
v_inv_2600_ = lean_ctor_get_uint8(v_a_2489_, 1);
lean_dec_ref(v_a_2489_);
v___x_2609_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2610_ = lean_name_eq(v_attrName_2454_, v___x_2609_);
lean_dec(v_attrName_2454_);
if (v___x_2610_ == 0)
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
lean_dec(v_declName_2449_);
v___x_2611_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13);
v___x_2612_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2611_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2612_;
}
else
{
v___y_2602_ = v___y_2455_;
v___y_2603_ = v___y_2456_;
v___y_2604_ = v___y_2457_;
v___y_2605_ = v___y_2458_;
goto v___jp_2601_;
}
v___jp_2601_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2606_ = l_Lean_Meta_Grind_normExt;
v___x_2607_ = lean_unsigned_to_nat(1000u);
v___x_2608_ = l_Lean_Meta_addSimpTheorem(v___x_2606_, v_declName_2449_, v_post_2599_, v_inv_2600_, v_attrKind_2450_, v___x_2607_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
return v___x_2608_;
}
}
default: 
{
lean_object* v___x_2613_; uint8_t v___x_2614_; 
lean_dec_ref(v_ext_2448_);
lean_dec(v_stx_2447_);
v___x_2613_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2614_ = lean_name_eq(v_attrName_2454_, v___x_2613_);
lean_dec(v_attrName_2454_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; lean_object* v___x_2616_; 
lean_dec(v_declName_2449_);
v___x_2615_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15);
v___x_2616_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2615_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2616_;
}
else
{
v___y_2461_ = v___y_2455_;
v___y_2462_ = v___y_2456_;
v___y_2463_ = v___y_2457_;
v___y_2464_ = v___y_2458_;
goto v___jp_2460_;
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v_attrName_2454_);
lean_dec(v_declName_2449_);
lean_dec_ref(v_ext_2448_);
lean_dec(v_stx_2447_);
v_a_2617_ = lean_ctor_get(v___x_2488_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2488_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2488_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2488_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
v___jp_2460_:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = l_Lean_Meta_Grind_normExt;
v___x_2466_ = lean_unsigned_to_nat(1000u);
v___x_2467_ = l_Lean_Meta_addDeclToUnfold(v___x_2465_, v_declName_2449_, v___x_2453_, v___x_2453_, v___x_2466_, v_attrKind_2450_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2479_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2470_ = v___x_2467_;
v_isShared_2471_ = v_isSharedCheck_2479_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2467_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2479_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
uint8_t v___x_2472_; 
v___x_2472_ = lean_unbox(v_a_2468_);
lean_dec(v_a_2468_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
lean_del_object(v___x_2470_);
v___x_2473_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_2474_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2473_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2474_;
}
else
{
lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2475_ = lean_box(0);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 0, v___x_2475_);
v___x_2477_ = v___x_2470_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
v_a_2480_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2467_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2467_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_stx_2625_, lean_object* v_ext_2626_, lean_object* v_declName_2627_, lean_object* v_attrKind_2628_, lean_object* v_showInfo_2629_, lean_object* v_minIndexable_2630_, lean_object* v___x_2631_, lean_object* v_attrName_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_){
_start:
{
uint8_t v_attrKind_boxed_2638_; uint8_t v_showInfo_boxed_2639_; uint8_t v_minIndexable_boxed_2640_; uint8_t v___x_15297__boxed_2641_; lean_object* v_res_2642_; 
v_attrKind_boxed_2638_ = lean_unbox(v_attrKind_2628_);
v_showInfo_boxed_2639_ = lean_unbox(v_showInfo_2629_);
v_minIndexable_boxed_2640_ = lean_unbox(v_minIndexable_2630_);
v___x_15297__boxed_2641_ = lean_unbox(v___x_2631_);
v_res_2642_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_stx_2625_, v_ext_2626_, v_declName_2627_, v_attrKind_boxed_2638_, v_showInfo_boxed_2639_, v_minIndexable_boxed_2640_, v___x_15297__boxed_2641_, v_attrName_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
return v_res_2642_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2643_; double v___x_2644_; 
v___x_2643_ = lean_unsigned_to_nat(0u);
v___x_2644_ = lean_float_of_nat(v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object* v_cls_2648_, lean_object* v_msg_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v_ref_2655_; lean_object* v___x_2656_; lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2701_; 
v_ref_2655_ = lean_ctor_get(v___y_2652_, 5);
v___x_2656_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2659_ = v___x_2656_;
v_isShared_2660_ = v_isSharedCheck_2701_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2656_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2701_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; lean_object* v_traceState_2662_; lean_object* v_env_2663_; lean_object* v_nextMacroScope_2664_; lean_object* v_ngen_2665_; lean_object* v_auxDeclNGen_2666_; lean_object* v_cache_2667_; lean_object* v_messages_2668_; lean_object* v_infoState_2669_; lean_object* v_snapshotTasks_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2700_; 
v___x_2661_ = lean_st_ref_take(v___y_2653_);
v_traceState_2662_ = lean_ctor_get(v___x_2661_, 4);
v_env_2663_ = lean_ctor_get(v___x_2661_, 0);
v_nextMacroScope_2664_ = lean_ctor_get(v___x_2661_, 1);
v_ngen_2665_ = lean_ctor_get(v___x_2661_, 2);
v_auxDeclNGen_2666_ = lean_ctor_get(v___x_2661_, 3);
v_cache_2667_ = lean_ctor_get(v___x_2661_, 5);
v_messages_2668_ = lean_ctor_get(v___x_2661_, 6);
v_infoState_2669_ = lean_ctor_get(v___x_2661_, 7);
v_snapshotTasks_2670_ = lean_ctor_get(v___x_2661_, 8);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2661_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2672_ = v___x_2661_;
v_isShared_2673_ = v_isSharedCheck_2700_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_snapshotTasks_2670_);
lean_inc(v_infoState_2669_);
lean_inc(v_messages_2668_);
lean_inc(v_cache_2667_);
lean_inc(v_traceState_2662_);
lean_inc(v_auxDeclNGen_2666_);
lean_inc(v_ngen_2665_);
lean_inc(v_nextMacroScope_2664_);
lean_inc(v_env_2663_);
lean_dec(v___x_2661_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2700_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
uint64_t v_tid_2674_; lean_object* v_traces_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2699_; 
v_tid_2674_ = lean_ctor_get_uint64(v_traceState_2662_, sizeof(void*)*1);
v_traces_2675_ = lean_ctor_get(v_traceState_2662_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v_traceState_2662_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2677_ = v_traceState_2662_;
v_isShared_2678_ = v_isSharedCheck_2699_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_traces_2675_);
lean_dec(v_traceState_2662_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2699_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2679_; double v___x_2680_; uint8_t v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2679_ = lean_box(0);
v___x_2680_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_2681_ = 0;
v___x_2682_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2683_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2683_, 0, v_cls_2648_);
lean_ctor_set(v___x_2683_, 1, v___x_2679_);
lean_ctor_set(v___x_2683_, 2, v___x_2682_);
lean_ctor_set_float(v___x_2683_, sizeof(void*)*3, v___x_2680_);
lean_ctor_set_float(v___x_2683_, sizeof(void*)*3 + 8, v___x_2680_);
lean_ctor_set_uint8(v___x_2683_, sizeof(void*)*3 + 16, v___x_2681_);
v___x_2684_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_2685_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2683_);
lean_ctor_set(v___x_2685_, 1, v_a_2657_);
lean_ctor_set(v___x_2685_, 2, v___x_2684_);
lean_inc(v_ref_2655_);
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v_ref_2655_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v___x_2687_ = l_Lean_PersistentArray_push___redArg(v_traces_2675_, v___x_2686_);
if (v_isShared_2678_ == 0)
{
lean_ctor_set(v___x_2677_, 0, v___x_2687_);
v___x_2689_ = v___x_2677_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2687_);
lean_ctor_set_uint64(v_reuseFailAlloc_2698_, sizeof(void*)*1, v_tid_2674_);
v___x_2689_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2691_; 
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 4, v___x_2689_);
v___x_2691_ = v___x_2672_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_env_2663_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_nextMacroScope_2664_);
lean_ctor_set(v_reuseFailAlloc_2697_, 2, v_ngen_2665_);
lean_ctor_set(v_reuseFailAlloc_2697_, 3, v_auxDeclNGen_2666_);
lean_ctor_set(v_reuseFailAlloc_2697_, 4, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2697_, 5, v_cache_2667_);
lean_ctor_set(v_reuseFailAlloc_2697_, 6, v_messages_2668_);
lean_ctor_set(v_reuseFailAlloc_2697_, 7, v_infoState_2669_);
lean_ctor_set(v_reuseFailAlloc_2697_, 8, v_snapshotTasks_2670_);
v___x_2691_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2695_; 
v___x_2692_ = lean_st_ref_set(v___y_2653_, v___x_2691_);
v___x_2693_ = lean_box(0);
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v___x_2693_);
v___x_2695_ = v___x_2659_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object* v_cls_2702_, lean_object* v_msg_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2702_, v_msg_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
return v_res_2709_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_keys_2710_, lean_object* v_i_2711_, lean_object* v_k_2712_){
_start:
{
lean_object* v___x_2713_; uint8_t v___x_2714_; 
v___x_2713_ = lean_array_get_size(v_keys_2710_);
v___x_2714_ = lean_nat_dec_lt(v_i_2711_, v___x_2713_);
if (v___x_2714_ == 0)
{
lean_dec(v_i_2711_);
return v___x_2714_;
}
else
{
lean_object* v_k_x27_2715_; uint8_t v___x_2716_; 
v_k_x27_2715_ = lean_array_fget_borrowed(v_keys_2710_, v_i_2711_);
v___x_2716_ = l_Lean_instBEqExtraModUse_beq(v_k_2712_, v_k_x27_2715_);
if (v___x_2716_ == 0)
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = lean_unsigned_to_nat(1u);
v___x_2718_ = lean_nat_add(v_i_2711_, v___x_2717_);
lean_dec(v_i_2711_);
v_i_2711_ = v___x_2718_;
goto _start;
}
else
{
lean_dec(v_i_2711_);
return v___x_2716_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_keys_2720_, lean_object* v_i_2721_, lean_object* v_k_2722_){
_start:
{
uint8_t v_res_2723_; lean_object* v_r_2724_; 
v_res_2723_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_2720_, v_i_2721_, v_k_2722_);
lean_dec_ref(v_k_2722_);
lean_dec_ref(v_keys_2720_);
v_r_2724_ = lean_box(v_res_2723_);
return v_r_2724_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2725_, size_t v_x_2726_, lean_object* v_x_2727_){
_start:
{
if (lean_obj_tag(v_x_2725_) == 0)
{
lean_object* v_es_2728_; lean_object* v___x_2729_; size_t v___x_2730_; size_t v___x_2731_; size_t v___x_2732_; lean_object* v_j_2733_; lean_object* v___x_2734_; 
v_es_2728_ = lean_ctor_get(v_x_2725_, 0);
v___x_2729_ = lean_box(2);
v___x_2730_ = ((size_t)5ULL);
v___x_2731_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1);
v___x_2732_ = lean_usize_land(v_x_2726_, v___x_2731_);
v_j_2733_ = lean_usize_to_nat(v___x_2732_);
v___x_2734_ = lean_array_get_borrowed(v___x_2729_, v_es_2728_, v_j_2733_);
lean_dec(v_j_2733_);
switch(lean_obj_tag(v___x_2734_))
{
case 0:
{
lean_object* v_key_2735_; uint8_t v___x_2736_; 
v_key_2735_ = lean_ctor_get(v___x_2734_, 0);
v___x_2736_ = l_Lean_instBEqExtraModUse_beq(v_x_2727_, v_key_2735_);
return v___x_2736_;
}
case 1:
{
lean_object* v_node_2737_; size_t v___x_2738_; 
v_node_2737_ = lean_ctor_get(v___x_2734_, 0);
v___x_2738_ = lean_usize_shift_right(v_x_2726_, v___x_2730_);
v_x_2725_ = v_node_2737_;
v_x_2726_ = v___x_2738_;
goto _start;
}
default: 
{
uint8_t v___x_2740_; 
v___x_2740_ = 0;
return v___x_2740_;
}
}
}
else
{
lean_object* v_ks_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v_ks_2741_ = lean_ctor_get(v_x_2725_, 0);
v___x_2742_ = lean_unsigned_to_nat(0u);
v___x_2743_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_ks_2741_, v___x_2742_, v_x_2727_);
return v___x_2743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2744_, lean_object* v_x_2745_, lean_object* v_x_2746_){
_start:
{
size_t v_x_15797__boxed_2747_; uint8_t v_res_2748_; lean_object* v_r_2749_; 
v_x_15797__boxed_2747_ = lean_unbox_usize(v_x_2745_);
lean_dec(v_x_2745_);
v_res_2748_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2744_, v_x_15797__boxed_2747_, v_x_2746_);
lean_dec_ref(v_x_2746_);
lean_dec_ref(v_x_2744_);
v_r_2749_ = lean_box(v_res_2748_);
return v_r_2749_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2750_, lean_object* v_x_2751_){
_start:
{
uint64_t v___x_2752_; size_t v___x_2753_; uint8_t v___x_2754_; 
v___x_2752_ = l_Lean_instHashableExtraModUse_hash(v_x_2751_);
v___x_2753_ = lean_uint64_to_usize(v___x_2752_);
v___x_2754_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2750_, v___x_2753_, v_x_2751_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_2755_, lean_object* v_x_2756_){
_start:
{
uint8_t v_res_2757_; lean_object* v_r_2758_; 
v_res_2757_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_2755_, v_x_2756_);
lean_dec_ref(v_x_2756_);
lean_dec_ref(v_x_2755_);
v_r_2758_ = lean_box(v_res_2757_);
return v_r_2758_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2761_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1));
v___x_2762_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0));
v___x_2763_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2762_, v___x_2761_);
return v___x_2763_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5));
v___x_2769_ = l_Lean_stringToMessageData(v___x_2768_);
return v___x_2769_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7));
v___x_2772_ = l_Lean_stringToMessageData(v___x_2771_);
return v___x_2772_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9(void){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2773_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2774_ = l_Lean_stringToMessageData(v___x_2773_);
return v___x_2774_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v_cls_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v_cls_2778_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_2779_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11));
v___x_2780_ = l_Lean_Name_append(v___x_2779_, v_cls_2778_);
return v___x_2780_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13));
v___x_2783_ = l_Lean_stringToMessageData(v___x_2782_);
return v___x_2783_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___x_2786_ = l_Lean_stringToMessageData(v___x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v_mod_2791_, uint8_t v_isMeta_2792_, lean_object* v_hint_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
lean_object* v___x_2799_; lean_object* v_env_2800_; uint8_t v_isExporting_2801_; lean_object* v___x_2802_; lean_object* v_env_2803_; lean_object* v___x_2804_; lean_object* v_entry_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v___x_2799_ = lean_st_ref_get(v___y_2797_);
v_env_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc_ref(v_env_2800_);
lean_dec(v___x_2799_);
v_isExporting_2801_ = lean_ctor_get_uint8(v_env_2800_, sizeof(void*)*8);
lean_dec_ref(v_env_2800_);
v___x_2802_ = lean_st_ref_get(v___y_2797_);
v_env_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc_ref(v_env_2803_);
lean_dec(v___x_2802_);
v___x_2804_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_2791_);
v_entry_2805_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2805_, 0, v_mod_2791_);
lean_ctor_set_uint8(v_entry_2805_, sizeof(void*)*1, v_isExporting_2801_);
lean_ctor_set_uint8(v_entry_2805_, sizeof(void*)*1 + 1, v_isMeta_2792_);
v___x_2806_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2807_ = lean_box(1);
v___x_2808_ = lean_box(0);
v___x_2851_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2804_, v___x_2806_, v_env_2803_, v___x_2807_, v___x_2808_);
v___x_2852_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_2851_, v_entry_2805_);
lean_dec(v___x_2851_);
if (v___x_2852_ == 0)
{
lean_object* v_options_2853_; uint8_t v_hasTrace_2854_; 
v_options_2853_ = lean_ctor_get(v___y_2796_, 2);
v_hasTrace_2854_ = lean_ctor_get_uint8(v_options_2853_, sizeof(void*)*1);
if (v_hasTrace_2854_ == 0)
{
lean_dec(v_hint_2793_);
lean_dec(v_mod_2791_);
v___y_2810_ = v___y_2795_;
v___y_2811_ = v___y_2797_;
goto v___jp_2809_;
}
else
{
lean_object* v_inheritedTraceOptions_2855_; lean_object* v_cls_2856_; lean_object* v___y_2858_; lean_object* v___y_2859_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v_inheritedTraceOptions_2855_ = lean_ctor_get(v___y_2796_, 13);
v_cls_2856_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_2876_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
v___x_2877_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2855_, v_options_2853_, v___x_2876_);
if (v___x_2877_ == 0)
{
lean_dec(v_hint_2793_);
lean_dec(v_mod_2791_);
v___y_2810_ = v___y_2795_;
v___y_2811_ = v___y_2797_;
goto v___jp_2809_;
}
else
{
lean_object* v___x_2878_; lean_object* v___y_2880_; 
v___x_2878_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
if (v_isExporting_2801_ == 0)
{
lean_object* v___x_2887_; 
v___x_2887_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19));
v___y_2880_ = v___x_2887_;
goto v___jp_2879_;
}
else
{
lean_object* v___x_2888_; 
v___x_2888_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20));
v___y_2880_ = v___x_2888_;
goto v___jp_2879_;
}
v___jp_2879_:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_inc_ref(v___y_2880_);
v___x_2881_ = l_Lean_stringToMessageData(v___y_2880_);
v___x_2882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2878_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
v___x_2883_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16);
v___x_2884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2882_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
if (v_isMeta_2792_ == 0)
{
lean_object* v___x_2885_; 
v___x_2885_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_2863_ = v___x_2884_;
v___y_2864_ = v___x_2885_;
goto v___jp_2862_;
}
else
{
lean_object* v___x_2886_; 
v___x_2886_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_2863_ = v___x_2884_;
v___y_2864_ = v___x_2886_;
goto v___jp_2862_;
}
}
}
v___jp_2857_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___y_2858_);
lean_ctor_set(v___x_2860_, 1, v___y_2859_);
v___x_2861_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2856_, v___x_2860_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_dec_ref(v___x_2861_);
v___y_2810_ = v___y_2795_;
v___y_2811_ = v___y_2797_;
goto v___jp_2809_;
}
else
{
lean_dec_ref(v_entry_2805_);
return v___x_2861_;
}
}
v___jp_2862_:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
lean_inc_ref(v___y_2864_);
v___x_2865_ = l_Lean_stringToMessageData(v___y_2864_);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___y_2863_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_2868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = l_Lean_MessageData_ofName(v_mod_2791_);
v___x_2870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2868_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v___x_2871_ = l_Lean_Name_isAnonymous(v_hint_2793_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2872_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_2873_ = l_Lean_MessageData_ofName(v_hint_2793_);
v___x_2874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2872_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___y_2858_ = v___x_2870_;
v___y_2859_ = v___x_2874_;
goto v___jp_2857_;
}
else
{
lean_object* v___x_2875_; 
lean_dec(v_hint_2793_);
v___x_2875_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_2858_ = v___x_2870_;
v___y_2859_ = v___x_2875_;
goto v___jp_2857_;
}
}
}
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
lean_dec_ref(v_entry_2805_);
lean_dec(v_hint_2793_);
lean_dec(v_mod_2791_);
v___x_2889_ = lean_box(0);
v___x_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2889_);
return v___x_2890_;
}
v___jp_2809_:
{
lean_object* v___x_2812_; lean_object* v_toEnvExtension_2813_; lean_object* v_env_2814_; lean_object* v_nextMacroScope_2815_; lean_object* v_ngen_2816_; lean_object* v_auxDeclNGen_2817_; lean_object* v_traceState_2818_; lean_object* v_messages_2819_; lean_object* v_infoState_2820_; lean_object* v_snapshotTasks_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2849_; 
v___x_2812_ = lean_st_ref_take(v___y_2811_);
v_toEnvExtension_2813_ = lean_ctor_get(v___x_2806_, 0);
v_env_2814_ = lean_ctor_get(v___x_2812_, 0);
v_nextMacroScope_2815_ = lean_ctor_get(v___x_2812_, 1);
v_ngen_2816_ = lean_ctor_get(v___x_2812_, 2);
v_auxDeclNGen_2817_ = lean_ctor_get(v___x_2812_, 3);
v_traceState_2818_ = lean_ctor_get(v___x_2812_, 4);
v_messages_2819_ = lean_ctor_get(v___x_2812_, 6);
v_infoState_2820_ = lean_ctor_get(v___x_2812_, 7);
v_snapshotTasks_2821_ = lean_ctor_get(v___x_2812_, 8);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v___x_2812_, 5);
lean_dec(v_unused_2850_);
v___x_2823_ = v___x_2812_;
v_isShared_2824_ = v_isSharedCheck_2849_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_snapshotTasks_2821_);
lean_inc(v_infoState_2820_);
lean_inc(v_messages_2819_);
lean_inc(v_traceState_2818_);
lean_inc(v_auxDeclNGen_2817_);
lean_inc(v_ngen_2816_);
lean_inc(v_nextMacroScope_2815_);
lean_inc(v_env_2814_);
lean_dec(v___x_2812_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2849_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v_asyncMode_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2829_; 
v_asyncMode_2825_ = lean_ctor_get(v_toEnvExtension_2813_, 2);
v___x_2826_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2806_, v_env_2814_, v_entry_2805_, v_asyncMode_2825_, v___x_2808_);
v___x_2827_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 5, v___x_2827_);
lean_ctor_set(v___x_2823_, 0, v___x_2826_);
v___x_2829_ = v___x_2823_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2826_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_nextMacroScope_2815_);
lean_ctor_set(v_reuseFailAlloc_2848_, 2, v_ngen_2816_);
lean_ctor_set(v_reuseFailAlloc_2848_, 3, v_auxDeclNGen_2817_);
lean_ctor_set(v_reuseFailAlloc_2848_, 4, v_traceState_2818_);
lean_ctor_set(v_reuseFailAlloc_2848_, 5, v___x_2827_);
lean_ctor_set(v_reuseFailAlloc_2848_, 6, v_messages_2819_);
lean_ctor_set(v_reuseFailAlloc_2848_, 7, v_infoState_2820_);
lean_ctor_set(v_reuseFailAlloc_2848_, 8, v_snapshotTasks_2821_);
v___x_2829_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v_mctx_2832_; lean_object* v_zetaDeltaFVarIds_2833_; lean_object* v_postponed_2834_; lean_object* v_diag_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2846_; 
v___x_2830_ = lean_st_ref_set(v___y_2811_, v___x_2829_);
v___x_2831_ = lean_st_ref_take(v___y_2810_);
v_mctx_2832_ = lean_ctor_get(v___x_2831_, 0);
v_zetaDeltaFVarIds_2833_ = lean_ctor_get(v___x_2831_, 2);
v_postponed_2834_ = lean_ctor_get(v___x_2831_, 3);
v_diag_2835_ = lean_ctor_get(v___x_2831_, 4);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; 
v_unused_2847_ = lean_ctor_get(v___x_2831_, 1);
lean_dec(v_unused_2847_);
v___x_2837_ = v___x_2831_;
v_isShared_2838_ = v_isSharedCheck_2846_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_diag_2835_);
lean_inc(v_postponed_2834_);
lean_inc(v_zetaDeltaFVarIds_2833_);
lean_inc(v_mctx_2832_);
lean_dec(v___x_2831_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2846_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v___x_2841_; 
v___x_2839_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 1, v___x_2839_);
v___x_2841_ = v___x_2837_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_mctx_2832_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v___x_2839_);
lean_ctor_set(v_reuseFailAlloc_2845_, 2, v_zetaDeltaFVarIds_2833_);
lean_ctor_set(v_reuseFailAlloc_2845_, 3, v_postponed_2834_);
lean_ctor_set(v_reuseFailAlloc_2845_, 4, v_diag_2835_);
v___x_2841_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2842_ = lean_st_ref_set(v___y_2810_, v___x_2841_);
v___x_2843_ = lean_box(0);
v___x_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
return v___x_2844_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v_mod_2891_, lean_object* v_isMeta_2892_, lean_object* v_hint_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_){
_start:
{
uint8_t v_isMeta_boxed_2899_; lean_object* v_res_2900_; 
v_isMeta_boxed_2899_ = lean_unbox(v_isMeta_2892_);
v_res_2900_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_mod_2891_, v_isMeta_boxed_2899_, v_hint_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_);
lean_dec(v___y_2897_);
lean_dec_ref(v___y_2896_);
lean_dec(v___y_2895_);
lean_dec_ref(v___y_2894_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object* v_a_2901_, lean_object* v_x_2902_){
_start:
{
if (lean_obj_tag(v_x_2902_) == 0)
{
lean_object* v___x_2903_; 
v___x_2903_ = lean_box(0);
return v___x_2903_;
}
else
{
lean_object* v_key_2904_; lean_object* v_value_2905_; lean_object* v_tail_2906_; uint8_t v___x_2907_; 
v_key_2904_ = lean_ctor_get(v_x_2902_, 0);
v_value_2905_ = lean_ctor_get(v_x_2902_, 1);
v_tail_2906_ = lean_ctor_get(v_x_2902_, 2);
v___x_2907_ = lean_name_eq(v_key_2904_, v_a_2901_);
if (v___x_2907_ == 0)
{
v_x_2902_ = v_tail_2906_;
goto _start;
}
else
{
lean_object* v___x_2909_; 
lean_inc(v_value_2905_);
v___x_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2909_, 0, v_value_2905_);
return v___x_2909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_a_2910_, lean_object* v_x_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2910_, v_x_2911_);
lean_dec(v_x_2911_);
lean_dec(v_a_2910_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object* v_m_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v_buckets_2915_; lean_object* v___x_2916_; uint64_t v___y_2918_; 
v_buckets_2915_ = lean_ctor_get(v_m_2913_, 1);
v___x_2916_ = lean_array_get_size(v_buckets_2915_);
if (lean_obj_tag(v_a_2914_) == 0)
{
uint64_t v___x_2932_; 
v___x_2932_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_2918_ = v___x_2932_;
goto v___jp_2917_;
}
else
{
uint64_t v_hash_2933_; 
v_hash_2933_ = lean_ctor_get_uint64(v_a_2914_, sizeof(void*)*2);
v___y_2918_ = v_hash_2933_;
goto v___jp_2917_;
}
v___jp_2917_:
{
uint64_t v___x_2919_; uint64_t v___x_2920_; uint64_t v_fold_2921_; uint64_t v___x_2922_; uint64_t v___x_2923_; uint64_t v___x_2924_; size_t v___x_2925_; size_t v___x_2926_; size_t v___x_2927_; size_t v___x_2928_; size_t v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2919_ = 32ULL;
v___x_2920_ = lean_uint64_shift_right(v___y_2918_, v___x_2919_);
v_fold_2921_ = lean_uint64_xor(v___y_2918_, v___x_2920_);
v___x_2922_ = 16ULL;
v___x_2923_ = lean_uint64_shift_right(v_fold_2921_, v___x_2922_);
v___x_2924_ = lean_uint64_xor(v_fold_2921_, v___x_2923_);
v___x_2925_ = lean_uint64_to_usize(v___x_2924_);
v___x_2926_ = lean_usize_of_nat(v___x_2916_);
v___x_2927_ = ((size_t)1ULL);
v___x_2928_ = lean_usize_sub(v___x_2926_, v___x_2927_);
v___x_2929_ = lean_usize_land(v___x_2925_, v___x_2928_);
v___x_2930_ = lean_array_uget_borrowed(v_buckets_2915_, v___x_2929_);
v___x_2931_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2914_, v___x_2930_);
return v___x_2931_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object* v_m_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_2934_, v_a_2935_);
lean_dec(v_a_2935_);
lean_dec_ref(v_m_2934_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v___x_2937_, lean_object* v_declName_2938_, lean_object* v_as_2939_, size_t v_sz_2940_, size_t v_i_2941_, lean_object* v_b_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
uint8_t v___x_2948_; 
v___x_2948_ = lean_usize_dec_lt(v_i_2941_, v_sz_2940_);
if (v___x_2948_ == 0)
{
lean_object* v___x_2949_; 
lean_dec(v_declName_2938_);
v___x_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2949_, 0, v_b_2942_);
return v___x_2949_;
}
else
{
lean_object* v___x_2950_; lean_object* v_modules_2951_; lean_object* v___x_2952_; lean_object* v_a_2953_; lean_object* v___x_2954_; lean_object* v_toImport_2955_; lean_object* v_module_2956_; uint8_t v___x_2957_; lean_object* v___x_2958_; 
v___x_2950_ = l_Lean_Environment_header(v___x_2937_);
v_modules_2951_ = lean_ctor_get(v___x_2950_, 3);
lean_inc_ref(v_modules_2951_);
lean_dec_ref(v___x_2950_);
v___x_2952_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2953_ = lean_array_uget_borrowed(v_as_2939_, v_i_2941_);
v___x_2954_ = lean_array_get(v___x_2952_, v_modules_2951_, v_a_2953_);
lean_dec_ref(v_modules_2951_);
v_toImport_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc_ref(v_toImport_2955_);
lean_dec(v___x_2954_);
v_module_2956_ = lean_ctor_get(v_toImport_2955_, 0);
lean_inc(v_module_2956_);
lean_dec_ref(v_toImport_2955_);
v___x_2957_ = 0;
lean_inc(v_declName_2938_);
v___x_2958_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_2956_, v___x_2957_, v_declName_2938_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v___x_2959_; size_t v___x_2960_; size_t v___x_2961_; 
lean_dec_ref(v___x_2958_);
v___x_2959_ = lean_box(0);
v___x_2960_ = ((size_t)1ULL);
v___x_2961_ = lean_usize_add(v_i_2941_, v___x_2960_);
v_i_2941_ = v___x_2961_;
v_b_2942_ = v___x_2959_;
goto _start;
}
else
{
lean_dec(v_declName_2938_);
return v___x_2958_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v___x_2963_, lean_object* v_declName_2964_, lean_object* v_as_2965_, lean_object* v_sz_2966_, lean_object* v_i_2967_, lean_object* v_b_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
size_t v_sz_boxed_2974_; size_t v_i_boxed_2975_; lean_object* v_res_2976_; 
v_sz_boxed_2974_ = lean_unbox_usize(v_sz_2966_);
lean_dec(v_sz_2966_);
v_i_boxed_2975_ = lean_unbox_usize(v_i_2967_);
lean_dec(v_i_2967_);
v_res_2976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v___x_2963_, v_declName_2964_, v_as_2965_, v_sz_boxed_2974_, v_i_boxed_2975_, v_b_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec_ref(v_as_2965_);
lean_dec_ref(v___x_2963_);
return v_res_2976_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2979_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___x_2980_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0));
v___x_2981_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2980_, v___x_2979_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_2984_, uint8_t v_isMeta_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v___x_2991_; lean_object* v_env_2995_; lean_object* v___y_2997_; lean_object* v___x_3010_; 
v___x_2991_ = lean_st_ref_get(v___y_2989_);
v_env_2995_ = lean_ctor_get(v___x_2991_, 0);
lean_inc_ref(v_env_2995_);
lean_dec(v___x_2991_);
v___x_3010_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2995_, v_declName_2984_);
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_dec_ref(v_env_2995_);
lean_dec(v_declName_2984_);
goto v___jp_2992_;
}
else
{
lean_object* v_val_3011_; lean_object* v___x_3012_; lean_object* v_modules_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v_val_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_val_3011_);
lean_dec_ref(v___x_3010_);
v___x_3012_ = l_Lean_Environment_header(v_env_2995_);
v_modules_3013_ = lean_ctor_get(v___x_3012_, 3);
lean_inc_ref(v_modules_3013_);
lean_dec_ref(v___x_3012_);
v___x_3014_ = lean_array_get_size(v_modules_3013_);
v___x_3015_ = lean_nat_dec_lt(v_val_3011_, v___x_3014_);
if (v___x_3015_ == 0)
{
lean_dec_ref(v_modules_3013_);
lean_dec(v_val_3011_);
lean_dec_ref(v_env_2995_);
lean_dec(v_declName_2984_);
goto v___jp_2992_;
}
else
{
lean_object* v___x_3016_; lean_object* v_env_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; uint8_t v___y_3021_; 
v___x_3016_ = lean_st_ref_get(v___y_2989_);
v_env_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc_ref(v_env_3017_);
lean_dec(v___x_3016_);
v___x_3018_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3019_ = lean_array_fget(v_modules_3013_, v_val_3011_);
lean_dec(v_val_3011_);
lean_dec_ref(v_modules_3013_);
if (v_isMeta_2985_ == 0)
{
lean_dec_ref(v_env_3017_);
v___y_3021_ = v_isMeta_2985_;
goto v___jp_3020_;
}
else
{
uint8_t v___x_3032_; 
lean_inc(v_declName_2984_);
v___x_3032_ = l_Lean_isMarkedMeta(v_env_3017_, v_declName_2984_);
if (v___x_3032_ == 0)
{
v___y_3021_ = v_isMeta_2985_;
goto v___jp_3020_;
}
else
{
uint8_t v___x_3033_; 
v___x_3033_ = 0;
v___y_3021_ = v___x_3033_;
goto v___jp_3020_;
}
}
v___jp_3020_:
{
lean_object* v_toImport_3022_; lean_object* v_module_3023_; lean_object* v___x_3024_; 
v_toImport_3022_ = lean_ctor_get(v___x_3019_, 0);
lean_inc_ref(v_toImport_3022_);
lean_dec(v___x_3019_);
v_module_3023_ = lean_ctor_get(v_toImport_3022_, 0);
lean_inc(v_module_3023_);
lean_dec_ref(v_toImport_3022_);
lean_inc(v_declName_2984_);
v___x_3024_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3023_, v___y_3021_, v_declName_2984_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
lean_dec_ref(v___x_3024_);
v___x_3025_ = l_Lean_indirectModUseExt;
v___x_3026_ = lean_box(1);
v___x_3027_ = lean_box(0);
lean_inc_ref(v_env_2995_);
v___x_3028_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3018_, v___x_3025_, v_env_2995_, v___x_3026_, v___x_3027_);
v___x_3029_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3028_, v_declName_2984_);
lean_dec(v___x_3028_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v___x_3030_; 
v___x_3030_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_2997_ = v___x_3030_;
goto v___jp_2996_;
}
else
{
lean_object* v_val_3031_; 
v_val_3031_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_val_3031_);
lean_dec_ref(v___x_3029_);
v___y_2997_ = v_val_3031_;
goto v___jp_2996_;
}
}
else
{
lean_dec_ref(v_env_2995_);
lean_dec(v_declName_2984_);
return v___x_3024_;
}
}
}
}
v___jp_2992_:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = lean_box(0);
v___x_2994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2994_, 0, v___x_2993_);
return v___x_2994_;
}
v___jp_2996_:
{
lean_object* v___x_2998_; size_t v_sz_2999_; size_t v___x_3000_; lean_object* v___x_3001_; 
v___x_2998_ = lean_box(0);
v_sz_2999_ = lean_array_size(v___y_2997_);
v___x_3000_ = ((size_t)0ULL);
v___x_3001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_env_2995_, v_declName_2984_, v___y_2997_, v_sz_2999_, v___x_3000_, v___x_2998_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
lean_dec_ref(v___y_2997_);
lean_dec_ref(v_env_2995_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3008_ == 0)
{
lean_object* v_unused_3009_; 
v_unused_3009_ = lean_ctor_get(v___x_3001_, 0);
lean_dec(v_unused_3009_);
v___x_3003_ = v___x_3001_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_dec(v___x_3001_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
lean_ctor_set(v___x_3003_, 0, v___x_2998_);
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_2998_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
else
{
return v___x_3001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_3034_, lean_object* v_isMeta_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_){
_start:
{
uint8_t v_isMeta_boxed_3041_; lean_object* v_res_3042_; 
v_isMeta_boxed_3041_ = lean_unbox(v_isMeta_3035_);
v_res_3042_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3034_, v_isMeta_boxed_3041_, v___y_3036_, v___y_3037_, v___y_3038_, v___y_3039_);
lean_dec(v___y_3039_);
lean_dec_ref(v___y_3038_);
lean_dec(v___y_3037_);
lean_dec_ref(v___y_3036_);
return v_res_3042_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object* v___y_3043_, uint8_t v_isExporting_3044_, lean_object* v___x_3045_, lean_object* v___y_3046_, lean_object* v___x_3047_, lean_object* v_a_x3f_3048_){
_start:
{
lean_object* v___x_3050_; lean_object* v_env_3051_; lean_object* v_nextMacroScope_3052_; lean_object* v_ngen_3053_; lean_object* v_auxDeclNGen_3054_; lean_object* v_traceState_3055_; lean_object* v_messages_3056_; lean_object* v_infoState_3057_; lean_object* v_snapshotTasks_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3083_; 
v___x_3050_ = lean_st_ref_take(v___y_3043_);
v_env_3051_ = lean_ctor_get(v___x_3050_, 0);
v_nextMacroScope_3052_ = lean_ctor_get(v___x_3050_, 1);
v_ngen_3053_ = lean_ctor_get(v___x_3050_, 2);
v_auxDeclNGen_3054_ = lean_ctor_get(v___x_3050_, 3);
v_traceState_3055_ = lean_ctor_get(v___x_3050_, 4);
v_messages_3056_ = lean_ctor_get(v___x_3050_, 6);
v_infoState_3057_ = lean_ctor_get(v___x_3050_, 7);
v_snapshotTasks_3058_ = lean_ctor_get(v___x_3050_, 8);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3083_ == 0)
{
lean_object* v_unused_3084_; 
v_unused_3084_ = lean_ctor_get(v___x_3050_, 5);
lean_dec(v_unused_3084_);
v___x_3060_ = v___x_3050_;
v_isShared_3061_ = v_isSharedCheck_3083_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_snapshotTasks_3058_);
lean_inc(v_infoState_3057_);
lean_inc(v_messages_3056_);
lean_inc(v_traceState_3055_);
lean_inc(v_auxDeclNGen_3054_);
lean_inc(v_ngen_3053_);
lean_inc(v_nextMacroScope_3052_);
lean_inc(v_env_3051_);
lean_dec(v___x_3050_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3083_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3062_; lean_object* v___x_3064_; 
v___x_3062_ = l_Lean_Environment_setExporting(v_env_3051_, v_isExporting_3044_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 5, v___x_3045_);
lean_ctor_set(v___x_3060_, 0, v___x_3062_);
v___x_3064_ = v___x_3060_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v___x_3062_);
lean_ctor_set(v_reuseFailAlloc_3082_, 1, v_nextMacroScope_3052_);
lean_ctor_set(v_reuseFailAlloc_3082_, 2, v_ngen_3053_);
lean_ctor_set(v_reuseFailAlloc_3082_, 3, v_auxDeclNGen_3054_);
lean_ctor_set(v_reuseFailAlloc_3082_, 4, v_traceState_3055_);
lean_ctor_set(v_reuseFailAlloc_3082_, 5, v___x_3045_);
lean_ctor_set(v_reuseFailAlloc_3082_, 6, v_messages_3056_);
lean_ctor_set(v_reuseFailAlloc_3082_, 7, v_infoState_3057_);
lean_ctor_set(v_reuseFailAlloc_3082_, 8, v_snapshotTasks_3058_);
v___x_3064_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v_mctx_3067_; lean_object* v_zetaDeltaFVarIds_3068_; lean_object* v_postponed_3069_; lean_object* v_diag_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3080_; 
v___x_3065_ = lean_st_ref_set(v___y_3043_, v___x_3064_);
v___x_3066_ = lean_st_ref_take(v___y_3046_);
v_mctx_3067_ = lean_ctor_get(v___x_3066_, 0);
v_zetaDeltaFVarIds_3068_ = lean_ctor_get(v___x_3066_, 2);
v_postponed_3069_ = lean_ctor_get(v___x_3066_, 3);
v_diag_3070_ = lean_ctor_get(v___x_3066_, 4);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3080_ == 0)
{
lean_object* v_unused_3081_; 
v_unused_3081_ = lean_ctor_get(v___x_3066_, 1);
lean_dec(v_unused_3081_);
v___x_3072_ = v___x_3066_;
v_isShared_3073_ = v_isSharedCheck_3080_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_diag_3070_);
lean_inc(v_postponed_3069_);
lean_inc(v_zetaDeltaFVarIds_3068_);
lean_inc(v_mctx_3067_);
lean_dec(v___x_3066_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3080_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
lean_ctor_set(v___x_3072_, 1, v___x_3047_);
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_mctx_3067_);
lean_ctor_set(v_reuseFailAlloc_3079_, 1, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3079_, 2, v_zetaDeltaFVarIds_3068_);
lean_ctor_set(v_reuseFailAlloc_3079_, 3, v_postponed_3069_);
lean_ctor_set(v_reuseFailAlloc_3079_, 4, v_diag_3070_);
v___x_3075_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3076_ = lean_st_ref_set(v___y_3046_, v___x_3075_);
v___x_3077_ = lean_box(0);
v___x_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
return v___x_3078_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object* v___y_3085_, lean_object* v_isExporting_3086_, lean_object* v___x_3087_, lean_object* v___y_3088_, lean_object* v___x_3089_, lean_object* v_a_x3f_3090_, lean_object* v___y_3091_){
_start:
{
uint8_t v_isExporting_boxed_3092_; lean_object* v_res_3093_; 
v_isExporting_boxed_3092_ = lean_unbox(v_isExporting_3086_);
v_res_3093_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3085_, v_isExporting_boxed_3092_, v___x_3087_, v___y_3088_, v___x_3089_, v_a_x3f_3090_);
lean_dec(v_a_x3f_3090_);
lean_dec(v___y_3088_);
lean_dec(v___y_3085_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object* v_x_3094_, uint8_t v_isExporting_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
lean_object* v___x_3101_; lean_object* v_env_3102_; uint8_t v_isExporting_3103_; lean_object* v___x_3104_; lean_object* v_env_3105_; lean_object* v_nextMacroScope_3106_; lean_object* v_ngen_3107_; lean_object* v_auxDeclNGen_3108_; lean_object* v_traceState_3109_; lean_object* v_messages_3110_; lean_object* v_infoState_3111_; lean_object* v_snapshotTasks_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3166_; 
v___x_3101_ = lean_st_ref_get(v___y_3099_);
v_env_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc_ref(v_env_3102_);
lean_dec(v___x_3101_);
v_isExporting_3103_ = lean_ctor_get_uint8(v_env_3102_, sizeof(void*)*8);
lean_dec_ref(v_env_3102_);
v___x_3104_ = lean_st_ref_take(v___y_3099_);
v_env_3105_ = lean_ctor_get(v___x_3104_, 0);
v_nextMacroScope_3106_ = lean_ctor_get(v___x_3104_, 1);
v_ngen_3107_ = lean_ctor_get(v___x_3104_, 2);
v_auxDeclNGen_3108_ = lean_ctor_get(v___x_3104_, 3);
v_traceState_3109_ = lean_ctor_get(v___x_3104_, 4);
v_messages_3110_ = lean_ctor_get(v___x_3104_, 6);
v_infoState_3111_ = lean_ctor_get(v___x_3104_, 7);
v_snapshotTasks_3112_ = lean_ctor_get(v___x_3104_, 8);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; 
v_unused_3167_ = lean_ctor_get(v___x_3104_, 5);
lean_dec(v_unused_3167_);
v___x_3114_ = v___x_3104_;
v_isShared_3115_ = v_isSharedCheck_3166_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_snapshotTasks_3112_);
lean_inc(v_infoState_3111_);
lean_inc(v_messages_3110_);
lean_inc(v_traceState_3109_);
lean_inc(v_auxDeclNGen_3108_);
lean_inc(v_ngen_3107_);
lean_inc(v_nextMacroScope_3106_);
lean_inc(v_env_3105_);
lean_dec(v___x_3104_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3166_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3116_ = l_Lean_Environment_setExporting(v_env_3105_, v_isExporting_3095_);
v___x_3117_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 5, v___x_3117_);
lean_ctor_set(v___x_3114_, 0, v___x_3116_);
v___x_3119_ = v___x_3114_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v_nextMacroScope_3106_);
lean_ctor_set(v_reuseFailAlloc_3165_, 2, v_ngen_3107_);
lean_ctor_set(v_reuseFailAlloc_3165_, 3, v_auxDeclNGen_3108_);
lean_ctor_set(v_reuseFailAlloc_3165_, 4, v_traceState_3109_);
lean_ctor_set(v_reuseFailAlloc_3165_, 5, v___x_3117_);
lean_ctor_set(v_reuseFailAlloc_3165_, 6, v_messages_3110_);
lean_ctor_set(v_reuseFailAlloc_3165_, 7, v_infoState_3111_);
lean_ctor_set(v_reuseFailAlloc_3165_, 8, v_snapshotTasks_3112_);
v___x_3119_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v_mctx_3122_; lean_object* v_zetaDeltaFVarIds_3123_; lean_object* v_postponed_3124_; lean_object* v_diag_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3163_; 
v___x_3120_ = lean_st_ref_set(v___y_3099_, v___x_3119_);
v___x_3121_ = lean_st_ref_take(v___y_3097_);
v_mctx_3122_ = lean_ctor_get(v___x_3121_, 0);
v_zetaDeltaFVarIds_3123_ = lean_ctor_get(v___x_3121_, 2);
v_postponed_3124_ = lean_ctor_get(v___x_3121_, 3);
v_diag_3125_ = lean_ctor_get(v___x_3121_, 4);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3163_ == 0)
{
lean_object* v_unused_3164_; 
v_unused_3164_ = lean_ctor_get(v___x_3121_, 1);
lean_dec(v_unused_3164_);
v___x_3127_ = v___x_3121_;
v_isShared_3128_ = v_isSharedCheck_3163_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_diag_3125_);
lean_inc(v_postponed_3124_);
lean_inc(v_zetaDeltaFVarIds_3123_);
lean_inc(v_mctx_3122_);
lean_dec(v___x_3121_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3163_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3129_; lean_object* v___x_3131_; 
v___x_3129_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_3128_ == 0)
{
lean_ctor_set(v___x_3127_, 1, v___x_3129_);
v___x_3131_ = v___x_3127_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_mctx_3122_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v___x_3129_);
lean_ctor_set(v_reuseFailAlloc_3162_, 2, v_zetaDeltaFVarIds_3123_);
lean_ctor_set(v_reuseFailAlloc_3162_, 3, v_postponed_3124_);
lean_ctor_set(v_reuseFailAlloc_3162_, 4, v_diag_3125_);
v___x_3131_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
lean_object* v___x_3132_; lean_object* v_r_3133_; 
v___x_3132_ = lean_st_ref_set(v___y_3097_, v___x_3131_);
lean_inc(v___y_3099_);
lean_inc_ref(v___y_3098_);
lean_inc(v___y_3097_);
lean_inc_ref(v___y_3096_);
v_r_3133_ = lean_apply_5(v_x_3094_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, lean_box(0));
if (lean_obj_tag(v_r_3133_) == 0)
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3150_; 
v_a_3134_ = lean_ctor_get(v_r_3133_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v_r_3133_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3136_ = v_r_3133_;
v_isShared_3137_ = v_isSharedCheck_3150_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v_r_3133_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3150_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
lean_inc(v_a_3134_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set_tag(v___x_3136_, 1);
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3134_);
v___x_3139_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
lean_object* v___x_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
v___x_3140_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3099_, v_isExporting_3103_, v___x_3117_, v___y_3097_, v___x_3129_, v___x_3139_);
lean_dec_ref(v___x_3139_);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3147_ == 0)
{
lean_object* v_unused_3148_; 
v_unused_3148_ = lean_ctor_get(v___x_3140_, 0);
lean_dec(v_unused_3148_);
v___x_3142_ = v___x_3140_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_dec(v___x_3140_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v_a_3134_);
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3134_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3160_; 
v_a_3151_ = lean_ctor_get(v_r_3133_, 0);
lean_inc(v_a_3151_);
lean_dec_ref(v_r_3133_);
v___x_3152_ = lean_box(0);
v___x_3153_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3099_, v_isExporting_3103_, v___x_3117_, v___y_3097_, v___x_3129_, v___x_3152_);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; 
v_unused_3161_ = lean_ctor_get(v___x_3153_, 0);
lean_dec(v_unused_3161_);
v___x_3155_ = v___x_3153_;
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
else
{
lean_dec(v___x_3153_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3160_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v___x_3158_; 
if (v_isShared_3156_ == 0)
{
lean_ctor_set_tag(v___x_3155_, 1);
lean_ctor_set(v___x_3155_, 0, v_a_3151_);
v___x_3158_ = v___x_3155_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3151_);
v___x_3158_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
return v___x_3158_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object* v_x_3168_, lean_object* v_isExporting_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
uint8_t v_isExporting_boxed_3175_; lean_object* v_res_3176_; 
v_isExporting_boxed_3175_ = lean_unbox(v_isExporting_3169_);
v_res_3176_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3168_, v_isExporting_boxed_3175_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_3177_, uint8_t v_when_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
if (v_when_3178_ == 0)
{
lean_object* v___x_3184_; 
lean_inc(v___y_3182_);
lean_inc_ref(v___y_3181_);
lean_inc(v___y_3180_);
lean_inc_ref(v___y_3179_);
v___x_3184_ = lean_apply_5(v_x_3177_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, lean_box(0));
return v___x_3184_;
}
else
{
uint8_t v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = 0;
v___x_3186_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3177_, v___x_3185_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
return v___x_3186_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_3187_, lean_object* v_when_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_){
_start:
{
uint8_t v_when_boxed_3194_; lean_object* v_res_3195_; 
v_when_boxed_3194_ = lean_unbox(v_when_3188_);
v_res_3195_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3187_, v_when_boxed_3194_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v___x_3196_, lean_object* v_ext_3197_, uint8_t v_showInfo_3198_, uint8_t v_minIndexable_3199_, lean_object* v_attrName_3200_, lean_object* v_declName_3201_, lean_object* v_stx_3202_, uint8_t v_attrKind_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
uint8_t v___x_3207_; uint8_t v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___y_3224_; lean_object* v___x_3234_; 
v___x_3207_ = 0;
v___x_3208_ = 1;
v___x_3209_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3210_ = lean_unsigned_to_nat(32u);
v___x_3211_ = lean_mk_empty_array_with_capacity(v___x_3210_);
lean_dec_ref(v___x_3211_);
v___x_3212_ = lean_unsigned_to_nat(0u);
v___x_3213_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_3214_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_3215_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6));
v___x_3216_ = lean_box(0);
lean_inc(v___x_3196_);
v___x_3217_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3217_, 0, v___x_3209_);
lean_ctor_set(v___x_3217_, 1, v___x_3196_);
lean_ctor_set(v___x_3217_, 2, v___x_3214_);
lean_ctor_set(v___x_3217_, 3, v___x_3215_);
lean_ctor_set(v___x_3217_, 4, v___x_3216_);
lean_ctor_set(v___x_3217_, 5, v___x_3212_);
lean_ctor_set(v___x_3217_, 6, v___x_3216_);
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*7, v___x_3207_);
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*7 + 1, v___x_3207_);
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*7 + 2, v___x_3207_);
lean_ctor_set_uint8(v___x_3217_, sizeof(void*)*7 + 3, v___x_3208_);
v___x_3218_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3219_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3220_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_3221_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3218_);
lean_ctor_set(v___x_3221_, 1, v___x_3219_);
lean_ctor_set(v___x_3221_, 2, v___x_3196_);
lean_ctor_set(v___x_3221_, 3, v___x_3213_);
lean_ctor_set(v___x_3221_, 4, v___x_3220_);
v___x_3222_ = lean_st_mk_ref(v___x_3221_);
lean_inc(v_declName_3201_);
v___x_3234_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3201_, v___x_3207_, v___x_3217_, v___x_3222_, v___y_3204_, v___y_3205_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___f_3239_; lean_object* v___x_3240_; 
lean_dec_ref(v___x_3234_);
v___x_3235_ = lean_box(v_attrKind_3203_);
v___x_3236_ = lean_box(v_showInfo_3198_);
v___x_3237_ = lean_box(v_minIndexable_3199_);
v___x_3238_ = lean_box(v___x_3207_);
v___f_3239_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_3239_, 0, v_stx_3202_);
lean_closure_set(v___f_3239_, 1, v_ext_3197_);
lean_closure_set(v___f_3239_, 2, v_declName_3201_);
lean_closure_set(v___f_3239_, 3, v___x_3235_);
lean_closure_set(v___f_3239_, 4, v___x_3236_);
lean_closure_set(v___f_3239_, 5, v___x_3237_);
lean_closure_set(v___f_3239_, 6, v___x_3238_);
lean_closure_set(v___f_3239_, 7, v_attrName_3200_);
v___x_3240_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_3239_, v___x_3208_, v___x_3217_, v___x_3222_, v___y_3204_, v___y_3205_);
lean_dec_ref(v___x_3217_);
v___y_3224_ = v___x_3240_;
goto v___jp_3223_;
}
else
{
lean_dec_ref(v___x_3217_);
lean_dec(v_stx_3202_);
lean_dec(v_declName_3201_);
lean_dec(v_attrName_3200_);
lean_dec_ref(v_ext_3197_);
v___y_3224_ = v___x_3234_;
goto v___jp_3223_;
}
v___jp_3223_:
{
if (lean_obj_tag(v___y_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3233_; 
v_a_3225_ = lean_ctor_get(v___y_3224_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___y_3224_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3227_ = v___y_3224_;
v_isShared_3228_ = v_isSharedCheck_3233_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_a_3225_);
lean_dec(v___y_3224_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3233_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3229_ = lean_st_ref_get(v___x_3222_);
lean_dec(v___x_3222_);
lean_dec(v___x_3229_);
if (v_isShared_3228_ == 0)
{
v___x_3231_ = v___x_3227_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3225_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
else
{
lean_dec(v___x_3222_);
return v___y_3224_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v___x_3241_, lean_object* v_ext_3242_, lean_object* v_showInfo_3243_, lean_object* v_minIndexable_3244_, lean_object* v_attrName_3245_, lean_object* v_declName_3246_, lean_object* v_stx_3247_, lean_object* v_attrKind_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_){
_start:
{
uint8_t v_showInfo_boxed_3252_; uint8_t v_minIndexable_boxed_3253_; uint8_t v_attrKind_boxed_3254_; lean_object* v_res_3255_; 
v_showInfo_boxed_3252_ = lean_unbox(v_showInfo_3243_);
v_minIndexable_boxed_3253_ = lean_unbox(v_minIndexable_3244_);
v_attrKind_boxed_3254_ = lean_unbox(v_attrKind_3248_);
v_res_3255_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v___x_3241_, v_ext_3242_, v_showInfo_boxed_3252_, v_minIndexable_boxed_3253_, v_attrName_3245_, v_declName_3246_, v_stx_3247_, v_attrKind_boxed_3254_, v___y_3249_, v___y_3250_);
lean_dec(v___y_3250_);
lean_dec_ref(v___y_3249_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_3278_, uint8_t v_minIndexable_3279_, uint8_t v_showInfo_3280_, lean_object* v_ext_3281_, lean_object* v_ref_3282_){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___f_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___f_3289_; lean_object* v___y_3291_; lean_object* v___y_3292_; lean_object* v___y_3335_; 
v___x_3284_ = lean_box(1);
v___x_3285_ = lean_box(v_showInfo_3280_);
lean_inc_n(v_attrName_3278_, 2);
lean_inc_ref(v_ext_3281_);
v___f_3286_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_3286_, 0, v___x_3284_);
lean_closure_set(v___f_3286_, 1, v_ext_3281_);
lean_closure_set(v___f_3286_, 2, v___x_3285_);
lean_closure_set(v___f_3286_, 3, v_attrName_3278_);
v___x_3287_ = lean_box(v_showInfo_3280_);
v___x_3288_ = lean_box(v_minIndexable_3279_);
v___f_3289_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_3289_, 0, v___x_3284_);
lean_closure_set(v___f_3289_, 1, v_ext_3281_);
lean_closure_set(v___f_3289_, 2, v___x_3287_);
lean_closure_set(v___f_3289_, 3, v___x_3288_);
lean_closure_set(v___f_3289_, 4, v_attrName_3278_);
if (v_minIndexable_3279_ == 0)
{
if (v_showInfo_3280_ == 0)
{
lean_inc(v_attrName_3278_);
v___y_3335_ = v_attrName_3278_;
goto v___jp_3334_;
}
else
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_3278_);
v___x_3364_ = lean_name_append_after(v_attrName_3278_, v___x_3363_);
v___y_3335_ = v___x_3364_;
goto v___jp_3334_;
}
}
else
{
if (v_showInfo_3280_ == 0)
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_3278_);
v___x_3366_ = lean_name_append_after(v_attrName_3278_, v___x_3365_);
v___y_3335_ = v___x_3366_;
goto v___jp_3334_;
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_3278_);
v___x_3368_ = lean_name_append_after(v_attrName_3278_, v___x_3367_);
v___y_3335_ = v___x_3368_;
goto v___jp_3334_;
}
}
v___jp_3290_:
{
lean_object* v___x_3293_; uint8_t v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; uint8_t v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3293_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_3294_ = 1;
v___x_3295_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3278_, v___x_3294_);
v___x_3296_ = lean_string_append(v___x_3293_, v___x_3295_);
v___x_3297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_3298_ = lean_string_append(v___x_3296_, v___x_3297_);
v___x_3299_ = lean_string_append(v___x_3298_, v___x_3295_);
v___x_3300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_3301_ = lean_string_append(v___x_3299_, v___x_3300_);
v___x_3302_ = lean_string_append(v___x_3301_, v___x_3295_);
v___x_3303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_3304_ = lean_string_append(v___x_3302_, v___x_3303_);
v___x_3305_ = lean_string_append(v___x_3304_, v___x_3295_);
v___x_3306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_3307_ = lean_string_append(v___x_3305_, v___x_3306_);
v___x_3308_ = lean_string_append(v___x_3307_, v___x_3295_);
v___x_3309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_3310_ = lean_string_append(v___x_3308_, v___x_3309_);
v___x_3311_ = lean_string_append(v___x_3310_, v___x_3295_);
v___x_3312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_3313_ = lean_string_append(v___x_3311_, v___x_3312_);
v___x_3314_ = lean_string_append(v___x_3313_, v___x_3295_);
v___x_3315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_3316_ = lean_string_append(v___x_3314_, v___x_3315_);
v___x_3317_ = lean_string_append(v___x_3316_, v___x_3295_);
v___x_3318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_3319_ = lean_string_append(v___x_3317_, v___x_3318_);
v___x_3320_ = lean_string_append(v___x_3319_, v___x_3295_);
v___x_3321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_3322_ = lean_string_append(v___x_3320_, v___x_3321_);
v___x_3323_ = lean_string_append(v___x_3322_, v___x_3295_);
v___x_3324_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_3325_ = lean_string_append(v___x_3323_, v___x_3324_);
v___x_3326_ = lean_string_append(v___x_3325_, v___x_3295_);
lean_dec_ref(v___x_3295_);
v___x_3327_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_3328_ = lean_string_append(v___x_3326_, v___x_3327_);
v___x_3329_ = lean_string_append(v___y_3292_, v___x_3328_);
lean_dec_ref(v___x_3328_);
v___x_3330_ = 1;
v___x_3331_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3331_, 0, v_ref_3282_);
lean_ctor_set(v___x_3331_, 1, v___y_3291_);
lean_ctor_set(v___x_3331_, 2, v___x_3329_);
lean_ctor_set_uint8(v___x_3331_, sizeof(void*)*3, v___x_3330_);
v___x_3332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3331_);
lean_ctor_set(v___x_3332_, 1, v___f_3289_);
lean_ctor_set(v___x_3332_, 2, v___f_3286_);
v___x_3333_ = l_Lean_registerBuiltinAttribute(v___x_3332_);
return v___x_3333_;
}
v___jp_3334_:
{
if (v_minIndexable_3279_ == 0)
{
if (v_showInfo_3280_ == 0)
{
lean_object* v___x_3336_; uint8_t v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_3337_ = 1;
lean_inc(v_attrName_3278_);
v___x_3338_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3278_, v___x_3337_);
v___x_3339_ = lean_string_append(v___x_3336_, v___x_3338_);
lean_dec_ref(v___x_3338_);
v___x_3340_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_3341_ = lean_string_append(v___x_3339_, v___x_3340_);
v___y_3291_ = v___y_3335_;
v___y_3292_ = v___x_3341_;
goto v___jp_3290_;
}
else
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v___x_3342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3278_);
v___x_3343_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3278_, v_showInfo_3280_);
v___x_3344_ = lean_string_append(v___x_3342_, v___x_3343_);
v___x_3345_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_3346_ = lean_string_append(v___x_3344_, v___x_3345_);
v___x_3347_ = lean_string_append(v___x_3346_, v___x_3343_);
lean_dec_ref(v___x_3343_);
v___x_3348_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_3349_ = lean_string_append(v___x_3347_, v___x_3348_);
v___y_3291_ = v___y_3335_;
v___y_3292_ = v___x_3349_;
goto v___jp_3290_;
}
}
else
{
if (v_showInfo_3280_ == 0)
{
lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3278_);
v___x_3351_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3278_, v_minIndexable_3279_);
v___x_3352_ = lean_string_append(v___x_3350_, v___x_3351_);
lean_dec_ref(v___x_3351_);
v___x_3353_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_3354_ = lean_string_append(v___x_3352_, v___x_3353_);
v___y_3291_ = v___y_3335_;
v___y_3292_ = v___x_3354_;
goto v___jp_3290_;
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3278_);
v___x_3356_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3278_, v_showInfo_3280_);
v___x_3357_ = lean_string_append(v___x_3355_, v___x_3356_);
v___x_3358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_3359_ = lean_string_append(v___x_3357_, v___x_3358_);
v___x_3360_ = lean_string_append(v___x_3359_, v___x_3356_);
lean_dec_ref(v___x_3356_);
v___x_3361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_3362_ = lean_string_append(v___x_3360_, v___x_3361_);
v___y_3291_ = v___y_3335_;
v___y_3292_ = v___x_3362_;
goto v___jp_3290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_3369_, lean_object* v_minIndexable_3370_, lean_object* v_showInfo_3371_, lean_object* v_ext_3372_, lean_object* v_ref_3373_, lean_object* v_a_3374_){
_start:
{
uint8_t v_minIndexable_boxed_3375_; uint8_t v_showInfo_boxed_3376_; lean_object* v_res_3377_; 
v_minIndexable_boxed_3375_ = lean_unbox(v_minIndexable_3370_);
v_showInfo_boxed_3376_ = lean_unbox(v_showInfo_3371_);
v_res_3377_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3369_, v_minIndexable_boxed_3375_, v_showInfo_boxed_3376_, v_ext_3372_, v_ref_3373_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_3378_, lean_object* v_msg_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_3386_, lean_object* v_msg_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_3386_, v_msg_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_3394_, uint8_t v_attrKind_3395_, uint8_t v_showInfo_3396_, uint8_t v_minIndexable_3397_, lean_object* v_as_3398_, lean_object* v_as_x27_3399_, lean_object* v_b_3400_, lean_object* v_a_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v___x_3407_; 
v___x_3407_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3394_, v_attrKind_3395_, v_showInfo_3396_, v_minIndexable_3397_, v_as_x27_3399_, v_b_3400_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_3408_, lean_object* v_attrKind_3409_, lean_object* v_showInfo_3410_, lean_object* v_minIndexable_3411_, lean_object* v_as_3412_, lean_object* v_as_x27_3413_, lean_object* v_b_3414_, lean_object* v_a_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
uint8_t v_attrKind_boxed_3421_; uint8_t v_showInfo_boxed_3422_; uint8_t v_minIndexable_boxed_3423_; lean_object* v_res_3424_; 
v_attrKind_boxed_3421_ = lean_unbox(v_attrKind_3409_);
v_showInfo_boxed_3422_ = lean_unbox(v_showInfo_3410_);
v_minIndexable_boxed_3423_ = lean_unbox(v_minIndexable_3411_);
v_res_3424_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_3408_, v_attrKind_boxed_3421_, v_showInfo_boxed_3422_, v_minIndexable_boxed_3423_, v_as_3412_, v_as_x27_3413_, v_b_3414_, v_a_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v_as_3412_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object* v_00_u03b1_3425_, lean_object* v_x_3426_, uint8_t v_isExporting_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v___x_3433_; 
v___x_3433_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3426_, v_isExporting_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3434_, lean_object* v_x_3435_, lean_object* v_isExporting_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
uint8_t v_isExporting_boxed_3442_; lean_object* v_res_3443_; 
v_isExporting_boxed_3442_ = lean_unbox(v_isExporting_3436_);
v_res_3443_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(v_00_u03b1_3434_, v_x_3435_, v_isExporting_boxed_3442_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_3444_, lean_object* v_x_3445_, uint8_t v_when_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3445_, v_when_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_3453_, lean_object* v_x_3454_, lean_object* v_when_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
uint8_t v_when_boxed_3461_; lean_object* v_res_3462_; 
v_when_boxed_3461_ = lean_unbox(v_when_3455_);
v_res_3462_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_3453_, v_x_3454_, v_when_boxed_3461_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
lean_dec(v___y_3457_);
lean_dec_ref(v___y_3456_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object* v_00_u03b2_3463_, lean_object* v_m_3464_, lean_object* v_a_3465_){
_start:
{
lean_object* v___x_3466_; 
v___x_3466_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_3464_, v_a_3465_);
return v___x_3466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3467_, lean_object* v_m_3468_, lean_object* v_a_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(v_00_u03b2_3467_, v_m_3468_, v_a_3469_);
lean_dec(v_a_3469_);
lean_dec_ref(v_m_3468_);
return v_res_3470_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3471_, lean_object* v_x_3472_, lean_object* v_x_3473_){
_start:
{
uint8_t v___x_3474_; 
v___x_3474_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_3472_, v_x_3473_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3475_, lean_object* v_x_3476_, lean_object* v_x_3477_){
_start:
{
uint8_t v_res_3478_; lean_object* v_r_3479_; 
v_res_3478_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(v_00_u03b2_3475_, v_x_3476_, v_x_3477_);
lean_dec_ref(v_x_3477_);
lean_dec_ref(v_x_3476_);
v_r_3479_ = lean_box(v_res_3478_);
return v_r_3479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_3480_, lean_object* v_a_3481_, lean_object* v_x_3482_){
_start:
{
lean_object* v___x_3483_; 
v___x_3483_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_3481_, v_x_3482_);
return v___x_3483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3484_, lean_object* v_a_3485_, lean_object* v_x_3486_){
_start:
{
lean_object* v_res_3487_; 
v_res_3487_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(v_00_u03b2_3484_, v_a_3485_, v_x_3486_);
lean_dec(v_x_3486_);
lean_dec(v_a_3485_);
return v_res_3487_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3488_, lean_object* v_x_3489_, size_t v_x_3490_, lean_object* v_x_3491_){
_start:
{
uint8_t v___x_3492_; 
v___x_3492_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_3489_, v_x_3490_, v_x_3491_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3493_, lean_object* v_x_3494_, lean_object* v_x_3495_, lean_object* v_x_3496_){
_start:
{
size_t v_x_17041__boxed_3497_; uint8_t v_res_3498_; lean_object* v_r_3499_; 
v_x_17041__boxed_3497_ = lean_unbox_usize(v_x_3495_);
lean_dec(v_x_3495_);
v_res_3498_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(v_00_u03b2_3493_, v_x_3494_, v_x_17041__boxed_3497_, v_x_3496_);
lean_dec_ref(v_x_3496_);
lean_dec_ref(v_x_3494_);
v_r_3499_ = lean_box(v_res_3498_);
return v_r_3499_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_3500_, lean_object* v_keys_3501_, lean_object* v_vals_3502_, lean_object* v_heq_3503_, lean_object* v_i_3504_, lean_object* v_k_3505_){
_start:
{
uint8_t v___x_3506_; 
v___x_3506_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_3501_, v_i_3504_, v_k_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3507_, lean_object* v_keys_3508_, lean_object* v_vals_3509_, lean_object* v_heq_3510_, lean_object* v_i_3511_, lean_object* v_k_3512_){
_start:
{
uint8_t v_res_3513_; lean_object* v_r_3514_; 
v_res_3513_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(v_00_u03b2_3507_, v_keys_3508_, v_vals_3509_, v_heq_3510_, v_i_3511_, v_k_3512_);
lean_dec_ref(v_k_3512_);
lean_dec_ref(v_vals_3509_);
lean_dec_ref(v_keys_3508_);
v_r_3514_ = lean_box(v_res_3513_);
return v_r_3514_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = lean_box(0);
v___x_3516_ = lean_unsigned_to_nat(16u);
v___x_3517_ = lean_mk_array(v___x_3516_, v___x_3515_);
return v___x_3517_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3518_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3519_ = lean_unsigned_to_nat(0u);
v___x_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3519_);
lean_ctor_set(v___x_3520_, 1, v___x_3518_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; 
v___x_3522_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3523_ = lean_st_mk_ref(v___x_3522_);
v___x_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_3527_, lean_object* v_msg_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_){
_start:
{
lean_object* v_ref_3532_; lean_object* v___x_3533_; lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3578_; 
v_ref_3532_ = lean_ctor_get(v___y_3529_, 5);
v___x_3533_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_3528_, v___y_3529_, v___y_3530_);
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3536_ = v___x_3533_;
v_isShared_3537_ = v_isSharedCheck_3578_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3533_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3578_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3538_; lean_object* v_traceState_3539_; lean_object* v_env_3540_; lean_object* v_nextMacroScope_3541_; lean_object* v_ngen_3542_; lean_object* v_auxDeclNGen_3543_; lean_object* v_cache_3544_; lean_object* v_messages_3545_; lean_object* v_infoState_3546_; lean_object* v_snapshotTasks_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3577_; 
v___x_3538_ = lean_st_ref_take(v___y_3530_);
v_traceState_3539_ = lean_ctor_get(v___x_3538_, 4);
v_env_3540_ = lean_ctor_get(v___x_3538_, 0);
v_nextMacroScope_3541_ = lean_ctor_get(v___x_3538_, 1);
v_ngen_3542_ = lean_ctor_get(v___x_3538_, 2);
v_auxDeclNGen_3543_ = lean_ctor_get(v___x_3538_, 3);
v_cache_3544_ = lean_ctor_get(v___x_3538_, 5);
v_messages_3545_ = lean_ctor_get(v___x_3538_, 6);
v_infoState_3546_ = lean_ctor_get(v___x_3538_, 7);
v_snapshotTasks_3547_ = lean_ctor_get(v___x_3538_, 8);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3549_ = v___x_3538_;
v_isShared_3550_ = v_isSharedCheck_3577_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_snapshotTasks_3547_);
lean_inc(v_infoState_3546_);
lean_inc(v_messages_3545_);
lean_inc(v_cache_3544_);
lean_inc(v_traceState_3539_);
lean_inc(v_auxDeclNGen_3543_);
lean_inc(v_ngen_3542_);
lean_inc(v_nextMacroScope_3541_);
lean_inc(v_env_3540_);
lean_dec(v___x_3538_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3577_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
uint64_t v_tid_3551_; lean_object* v_traces_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3576_; 
v_tid_3551_ = lean_ctor_get_uint64(v_traceState_3539_, sizeof(void*)*1);
v_traces_3552_ = lean_ctor_get(v_traceState_3539_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v_traceState_3539_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3554_ = v_traceState_3539_;
v_isShared_3555_ = v_isSharedCheck_3576_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_traces_3552_);
lean_dec(v_traceState_3539_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3576_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3556_; double v___x_3557_; uint8_t v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3566_; 
v___x_3556_ = lean_box(0);
v___x_3557_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_3558_ = 0;
v___x_3559_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_3560_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3560_, 0, v_cls_3527_);
lean_ctor_set(v___x_3560_, 1, v___x_3556_);
lean_ctor_set(v___x_3560_, 2, v___x_3559_);
lean_ctor_set_float(v___x_3560_, sizeof(void*)*3, v___x_3557_);
lean_ctor_set_float(v___x_3560_, sizeof(void*)*3 + 8, v___x_3557_);
lean_ctor_set_uint8(v___x_3560_, sizeof(void*)*3 + 16, v___x_3558_);
v___x_3561_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_3562_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3560_);
lean_ctor_set(v___x_3562_, 1, v_a_3534_);
lean_ctor_set(v___x_3562_, 2, v___x_3561_);
lean_inc(v_ref_3532_);
v___x_3563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3563_, 0, v_ref_3532_);
lean_ctor_set(v___x_3563_, 1, v___x_3562_);
v___x_3564_ = l_Lean_PersistentArray_push___redArg(v_traces_3552_, v___x_3563_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v___x_3564_);
v___x_3566_ = v___x_3554_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v___x_3564_);
lean_ctor_set_uint64(v_reuseFailAlloc_3575_, sizeof(void*)*1, v_tid_3551_);
v___x_3566_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
lean_object* v___x_3568_; 
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 4, v___x_3566_);
v___x_3568_ = v___x_3549_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_env_3540_);
lean_ctor_set(v_reuseFailAlloc_3574_, 1, v_nextMacroScope_3541_);
lean_ctor_set(v_reuseFailAlloc_3574_, 2, v_ngen_3542_);
lean_ctor_set(v_reuseFailAlloc_3574_, 3, v_auxDeclNGen_3543_);
lean_ctor_set(v_reuseFailAlloc_3574_, 4, v___x_3566_);
lean_ctor_set(v_reuseFailAlloc_3574_, 5, v_cache_3544_);
lean_ctor_set(v_reuseFailAlloc_3574_, 6, v_messages_3545_);
lean_ctor_set(v_reuseFailAlloc_3574_, 7, v_infoState_3546_);
lean_ctor_set(v_reuseFailAlloc_3574_, 8, v_snapshotTasks_3547_);
v___x_3568_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3569_ = lean_st_ref_set(v___y_3530_, v___x_3568_);
v___x_3570_ = lean_box(0);
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 0, v___x_3570_);
v___x_3572_ = v___x_3536_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v___x_3570_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_3579_, lean_object* v_msg_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3579_, v_msg_3580_, v___y_3581_, v___y_3582_);
lean_dec(v___y_3582_);
lean_dec_ref(v___y_3581_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_3585_, uint8_t v_isMeta_3586_, lean_object* v_hint_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_){
_start:
{
lean_object* v___x_3591_; lean_object* v_env_3592_; uint8_t v_isExporting_3593_; lean_object* v___x_3594_; lean_object* v_env_3595_; lean_object* v___x_3596_; lean_object* v_entry_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___y_3602_; lean_object* v___x_3627_; uint8_t v___x_3628_; 
v___x_3591_ = lean_st_ref_get(v___y_3589_);
v_env_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc_ref(v_env_3592_);
lean_dec(v___x_3591_);
v_isExporting_3593_ = lean_ctor_get_uint8(v_env_3592_, sizeof(void*)*8);
lean_dec_ref(v_env_3592_);
v___x_3594_ = lean_st_ref_get(v___y_3589_);
v_env_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc_ref(v_env_3595_);
lean_dec(v___x_3594_);
v___x_3596_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_3585_);
v_entry_3597_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3597_, 0, v_mod_3585_);
lean_ctor_set_uint8(v_entry_3597_, sizeof(void*)*1, v_isExporting_3593_);
lean_ctor_set_uint8(v_entry_3597_, sizeof(void*)*1 + 1, v_isMeta_3586_);
v___x_3598_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3599_ = lean_box(1);
v___x_3600_ = lean_box(0);
v___x_3627_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3596_, v___x_3598_, v_env_3595_, v___x_3599_, v___x_3600_);
v___x_3628_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_3627_, v_entry_3597_);
lean_dec(v___x_3627_);
if (v___x_3628_ == 0)
{
lean_object* v_options_3629_; uint8_t v_hasTrace_3630_; 
v_options_3629_ = lean_ctor_get(v___y_3588_, 2);
v_hasTrace_3630_ = lean_ctor_get_uint8(v_options_3629_, sizeof(void*)*1);
if (v_hasTrace_3630_ == 0)
{
lean_dec(v_hint_3587_);
lean_dec(v_mod_3585_);
v___y_3602_ = v___y_3589_;
goto v___jp_3601_;
}
else
{
lean_object* v_inheritedTraceOptions_3631_; lean_object* v_cls_3632_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___y_3639_; lean_object* v___y_3640_; lean_object* v___x_3652_; uint8_t v___x_3653_; 
v_inheritedTraceOptions_3631_ = lean_ctor_get(v___y_3588_, 13);
v_cls_3632_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_3652_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
v___x_3653_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3631_, v_options_3629_, v___x_3652_);
if (v___x_3653_ == 0)
{
lean_dec(v_hint_3587_);
lean_dec(v_mod_3585_);
v___y_3602_ = v___y_3589_;
goto v___jp_3601_;
}
else
{
lean_object* v___x_3654_; lean_object* v___y_3656_; 
v___x_3654_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
if (v_isExporting_3593_ == 0)
{
lean_object* v___x_3663_; 
v___x_3663_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19));
v___y_3656_ = v___x_3663_;
goto v___jp_3655_;
}
else
{
lean_object* v___x_3664_; 
v___x_3664_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20));
v___y_3656_ = v___x_3664_;
goto v___jp_3655_;
}
v___jp_3655_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
lean_inc_ref(v___y_3656_);
v___x_3657_ = l_Lean_stringToMessageData(v___y_3656_);
v___x_3658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3654_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
v___x_3659_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16);
v___x_3660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3658_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
if (v_isMeta_3586_ == 0)
{
lean_object* v___x_3661_; 
v___x_3661_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_3639_ = v___x_3660_;
v___y_3640_ = v___x_3661_;
goto v___jp_3638_;
}
else
{
lean_object* v___x_3662_; 
v___x_3662_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_3639_ = v___x_3660_;
v___y_3640_ = v___x_3662_;
goto v___jp_3638_;
}
}
}
v___jp_3633_:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; 
v___x_3636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3636_, 0, v___y_3634_);
lean_ctor_set(v___x_3636_, 1, v___y_3635_);
v___x_3637_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3632_, v___x_3636_, v___y_3588_, v___y_3589_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_dec_ref(v___x_3637_);
v___y_3602_ = v___y_3589_;
goto v___jp_3601_;
}
else
{
lean_dec_ref(v_entry_3597_);
return v___x_3637_;
}
}
v___jp_3638_:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; uint8_t v___x_3647_; 
lean_inc_ref(v___y_3640_);
v___x_3641_ = l_Lean_stringToMessageData(v___y_3640_);
v___x_3642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3642_, 0, v___y_3639_);
lean_ctor_set(v___x_3642_, 1, v___x_3641_);
v___x_3643_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_3644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3642_);
lean_ctor_set(v___x_3644_, 1, v___x_3643_);
v___x_3645_ = l_Lean_MessageData_ofName(v_mod_3585_);
v___x_3646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3644_);
lean_ctor_set(v___x_3646_, 1, v___x_3645_);
v___x_3647_ = l_Lean_Name_isAnonymous(v_hint_3587_);
if (v___x_3647_ == 0)
{
lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3648_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_3649_ = l_Lean_MessageData_ofName(v_hint_3587_);
v___x_3650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3648_);
lean_ctor_set(v___x_3650_, 1, v___x_3649_);
v___y_3634_ = v___x_3646_;
v___y_3635_ = v___x_3650_;
goto v___jp_3633_;
}
else
{
lean_object* v___x_3651_; 
lean_dec(v_hint_3587_);
v___x_3651_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_3634_ = v___x_3646_;
v___y_3635_ = v___x_3651_;
goto v___jp_3633_;
}
}
}
}
else
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
lean_dec_ref(v_entry_3597_);
lean_dec(v_hint_3587_);
lean_dec(v_mod_3585_);
v___x_3665_ = lean_box(0);
v___x_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3665_);
return v___x_3666_;
}
v___jp_3601_:
{
lean_object* v___x_3603_; lean_object* v_toEnvExtension_3604_; lean_object* v_env_3605_; lean_object* v_nextMacroScope_3606_; lean_object* v_ngen_3607_; lean_object* v_auxDeclNGen_3608_; lean_object* v_traceState_3609_; lean_object* v_messages_3610_; lean_object* v_infoState_3611_; lean_object* v_snapshotTasks_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3625_; 
v___x_3603_ = lean_st_ref_take(v___y_3602_);
v_toEnvExtension_3604_ = lean_ctor_get(v___x_3598_, 0);
v_env_3605_ = lean_ctor_get(v___x_3603_, 0);
v_nextMacroScope_3606_ = lean_ctor_get(v___x_3603_, 1);
v_ngen_3607_ = lean_ctor_get(v___x_3603_, 2);
v_auxDeclNGen_3608_ = lean_ctor_get(v___x_3603_, 3);
v_traceState_3609_ = lean_ctor_get(v___x_3603_, 4);
v_messages_3610_ = lean_ctor_get(v___x_3603_, 6);
v_infoState_3611_ = lean_ctor_get(v___x_3603_, 7);
v_snapshotTasks_3612_ = lean_ctor_get(v___x_3603_, 8);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3625_ == 0)
{
lean_object* v_unused_3626_; 
v_unused_3626_ = lean_ctor_get(v___x_3603_, 5);
lean_dec(v_unused_3626_);
v___x_3614_ = v___x_3603_;
v_isShared_3615_ = v_isSharedCheck_3625_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_snapshotTasks_3612_);
lean_inc(v_infoState_3611_);
lean_inc(v_messages_3610_);
lean_inc(v_traceState_3609_);
lean_inc(v_auxDeclNGen_3608_);
lean_inc(v_ngen_3607_);
lean_inc(v_nextMacroScope_3606_);
lean_inc(v_env_3605_);
lean_dec(v___x_3603_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3625_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v_asyncMode_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3620_; 
v_asyncMode_3616_ = lean_ctor_get(v_toEnvExtension_3604_, 2);
v___x_3617_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3598_, v_env_3605_, v_entry_3597_, v_asyncMode_3616_, v___x_3600_);
v___x_3618_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3615_ == 0)
{
lean_ctor_set(v___x_3614_, 5, v___x_3618_);
lean_ctor_set(v___x_3614_, 0, v___x_3617_);
v___x_3620_ = v___x_3614_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3617_);
lean_ctor_set(v_reuseFailAlloc_3624_, 1, v_nextMacroScope_3606_);
lean_ctor_set(v_reuseFailAlloc_3624_, 2, v_ngen_3607_);
lean_ctor_set(v_reuseFailAlloc_3624_, 3, v_auxDeclNGen_3608_);
lean_ctor_set(v_reuseFailAlloc_3624_, 4, v_traceState_3609_);
lean_ctor_set(v_reuseFailAlloc_3624_, 5, v___x_3618_);
lean_ctor_set(v_reuseFailAlloc_3624_, 6, v_messages_3610_);
lean_ctor_set(v_reuseFailAlloc_3624_, 7, v_infoState_3611_);
lean_ctor_set(v_reuseFailAlloc_3624_, 8, v_snapshotTasks_3612_);
v___x_3620_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3621_ = lean_st_ref_set(v___y_3602_, v___x_3620_);
v___x_3622_ = lean_box(0);
v___x_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
return v___x_3623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_3667_, lean_object* v_isMeta_3668_, lean_object* v_hint_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
uint8_t v_isMeta_boxed_3673_; lean_object* v_res_3674_; 
v_isMeta_boxed_3673_ = lean_unbox(v_isMeta_3668_);
v_res_3674_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_3667_, v_isMeta_boxed_3673_, v_hint_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
return v_res_3674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_3675_, lean_object* v_declName_3676_, lean_object* v_as_3677_, size_t v_sz_3678_, size_t v_i_3679_, lean_object* v_b_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
uint8_t v___x_3684_; 
v___x_3684_ = lean_usize_dec_lt(v_i_3679_, v_sz_3678_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3685_; 
lean_dec(v_declName_3676_);
v___x_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3685_, 0, v_b_3680_);
return v___x_3685_;
}
else
{
lean_object* v___x_3686_; lean_object* v_modules_3687_; lean_object* v___x_3688_; lean_object* v_a_3689_; lean_object* v___x_3690_; lean_object* v_toImport_3691_; lean_object* v_module_3692_; uint8_t v___x_3693_; lean_object* v___x_3694_; 
v___x_3686_ = l_Lean_Environment_header(v___x_3675_);
v_modules_3687_ = lean_ctor_get(v___x_3686_, 3);
lean_inc_ref(v_modules_3687_);
lean_dec_ref(v___x_3686_);
v___x_3688_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3689_ = lean_array_uget_borrowed(v_as_3677_, v_i_3679_);
v___x_3690_ = lean_array_get(v___x_3688_, v_modules_3687_, v_a_3689_);
lean_dec_ref(v_modules_3687_);
v_toImport_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc_ref(v_toImport_3691_);
lean_dec(v___x_3690_);
v_module_3692_ = lean_ctor_get(v_toImport_3691_, 0);
lean_inc(v_module_3692_);
lean_dec_ref(v_toImport_3691_);
v___x_3693_ = 0;
lean_inc(v_declName_3676_);
v___x_3694_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3692_, v___x_3693_, v_declName_3676_, v___y_3681_, v___y_3682_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v___x_3695_; size_t v___x_3696_; size_t v___x_3697_; 
lean_dec_ref(v___x_3694_);
v___x_3695_ = lean_box(0);
v___x_3696_ = ((size_t)1ULL);
v___x_3697_ = lean_usize_add(v_i_3679_, v___x_3696_);
v_i_3679_ = v___x_3697_;
v_b_3680_ = v___x_3695_;
goto _start;
}
else
{
lean_dec(v_declName_3676_);
return v___x_3694_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_3699_, lean_object* v_declName_3700_, lean_object* v_as_3701_, lean_object* v_sz_3702_, lean_object* v_i_3703_, lean_object* v_b_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
size_t v_sz_boxed_3708_; size_t v_i_boxed_3709_; lean_object* v_res_3710_; 
v_sz_boxed_3708_ = lean_unbox_usize(v_sz_3702_);
lean_dec(v_sz_3702_);
v_i_boxed_3709_ = lean_unbox_usize(v_i_3703_);
lean_dec(v_i_3703_);
v_res_3710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_3699_, v_declName_3700_, v_as_3701_, v_sz_boxed_3708_, v_i_boxed_3709_, v_b_3704_, v___y_3705_, v___y_3706_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec_ref(v_as_3701_);
lean_dec_ref(v___x_3699_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_3711_, uint8_t v_isMeta_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
lean_object* v___x_3716_; lean_object* v_env_3720_; lean_object* v___y_3722_; lean_object* v___x_3735_; 
v___x_3716_ = lean_st_ref_get(v___y_3714_);
v_env_3720_ = lean_ctor_get(v___x_3716_, 0);
lean_inc_ref(v_env_3720_);
lean_dec(v___x_3716_);
v___x_3735_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3720_, v_declName_3711_);
if (lean_obj_tag(v___x_3735_) == 0)
{
lean_dec_ref(v_env_3720_);
lean_dec(v_declName_3711_);
goto v___jp_3717_;
}
else
{
lean_object* v_val_3736_; lean_object* v___x_3737_; lean_object* v_modules_3738_; lean_object* v___x_3739_; uint8_t v___x_3740_; 
v_val_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc(v_val_3736_);
lean_dec_ref(v___x_3735_);
v___x_3737_ = l_Lean_Environment_header(v_env_3720_);
v_modules_3738_ = lean_ctor_get(v___x_3737_, 3);
lean_inc_ref(v_modules_3738_);
lean_dec_ref(v___x_3737_);
v___x_3739_ = lean_array_get_size(v_modules_3738_);
v___x_3740_ = lean_nat_dec_lt(v_val_3736_, v___x_3739_);
if (v___x_3740_ == 0)
{
lean_dec_ref(v_modules_3738_);
lean_dec(v_val_3736_);
lean_dec_ref(v_env_3720_);
lean_dec(v_declName_3711_);
goto v___jp_3717_;
}
else
{
lean_object* v___x_3741_; lean_object* v_env_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; uint8_t v___y_3746_; 
v___x_3741_ = lean_st_ref_get(v___y_3714_);
v_env_3742_ = lean_ctor_get(v___x_3741_, 0);
lean_inc_ref(v_env_3742_);
lean_dec(v___x_3741_);
v___x_3743_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3744_ = lean_array_fget(v_modules_3738_, v_val_3736_);
lean_dec(v_val_3736_);
lean_dec_ref(v_modules_3738_);
if (v_isMeta_3712_ == 0)
{
lean_dec_ref(v_env_3742_);
v___y_3746_ = v_isMeta_3712_;
goto v___jp_3745_;
}
else
{
uint8_t v___x_3757_; 
lean_inc(v_declName_3711_);
v___x_3757_ = l_Lean_isMarkedMeta(v_env_3742_, v_declName_3711_);
if (v___x_3757_ == 0)
{
v___y_3746_ = v_isMeta_3712_;
goto v___jp_3745_;
}
else
{
uint8_t v___x_3758_; 
v___x_3758_ = 0;
v___y_3746_ = v___x_3758_;
goto v___jp_3745_;
}
}
v___jp_3745_:
{
lean_object* v_toImport_3747_; lean_object* v_module_3748_; lean_object* v___x_3749_; 
v_toImport_3747_ = lean_ctor_get(v___x_3744_, 0);
lean_inc_ref(v_toImport_3747_);
lean_dec(v___x_3744_);
v_module_3748_ = lean_ctor_get(v_toImport_3747_, 0);
lean_inc(v_module_3748_);
lean_dec_ref(v_toImport_3747_);
lean_inc(v_declName_3711_);
v___x_3749_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3748_, v___y_3746_, v_declName_3711_, v___y_3713_, v___y_3714_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
lean_dec_ref(v___x_3749_);
v___x_3750_ = l_Lean_indirectModUseExt;
v___x_3751_ = lean_box(1);
v___x_3752_ = lean_box(0);
lean_inc_ref(v_env_3720_);
v___x_3753_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3743_, v___x_3750_, v_env_3720_, v___x_3751_, v___x_3752_);
v___x_3754_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3753_, v_declName_3711_);
lean_dec(v___x_3753_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v___x_3755_; 
v___x_3755_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_3722_ = v___x_3755_;
goto v___jp_3721_;
}
else
{
lean_object* v_val_3756_; 
v_val_3756_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_val_3756_);
lean_dec_ref(v___x_3754_);
v___y_3722_ = v_val_3756_;
goto v___jp_3721_;
}
}
else
{
lean_dec_ref(v_env_3720_);
lean_dec(v_declName_3711_);
return v___x_3749_;
}
}
}
}
v___jp_3717_:
{
lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3718_ = lean_box(0);
v___x_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3718_);
return v___x_3719_;
}
v___jp_3721_:
{
lean_object* v___x_3723_; size_t v_sz_3724_; size_t v___x_3725_; lean_object* v___x_3726_; 
v___x_3723_ = lean_box(0);
v_sz_3724_ = lean_array_size(v___y_3722_);
v___x_3725_ = ((size_t)0ULL);
v___x_3726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_3720_, v_declName_3711_, v___y_3722_, v_sz_3724_, v___x_3725_, v___x_3723_, v___y_3713_, v___y_3714_);
lean_dec_ref(v___y_3722_);
lean_dec_ref(v_env_3720_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3733_ == 0)
{
lean_object* v_unused_3734_; 
v_unused_3734_ = lean_ctor_get(v___x_3726_, 0);
lean_dec(v_unused_3734_);
v___x_3728_ = v___x_3726_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_dec(v___x_3726_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
lean_ctor_set(v___x_3728_, 0, v___x_3723_);
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3723_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
else
{
return v___x_3726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_3759_, lean_object* v_isMeta_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
uint8_t v_isMeta_boxed_3764_; lean_object* v_res_3765_; 
v_isMeta_boxed_3764_ = lean_unbox(v_isMeta_3760_);
v_res_3765_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_3759_, v_isMeta_boxed_3764_, v___y_3761_, v___y_3762_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
return v_res_3765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_){
_start:
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3770_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3771_ = lean_st_ref_get(v___x_3770_);
v___x_3772_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3771_, v_attrName_3766_);
lean_dec(v___x_3771_);
if (lean_obj_tag(v___x_3772_) == 1)
{
lean_object* v_val_3773_; lean_object* v_ext_3774_; lean_object* v_name_3775_; uint8_t v___x_3776_; lean_object* v___x_3777_; 
v_val_3773_ = lean_ctor_get(v___x_3772_, 0);
lean_inc(v_val_3773_);
v_ext_3774_ = lean_ctor_get(v_val_3773_, 1);
lean_inc_ref(v_ext_3774_);
lean_dec(v_val_3773_);
v_name_3775_ = lean_ctor_get(v_ext_3774_, 1);
lean_inc(v_name_3775_);
lean_dec_ref(v_ext_3774_);
v___x_3776_ = 1;
v___x_3777_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_3775_, v___x_3776_, v_a_3767_, v_a_3768_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3784_ == 0)
{
lean_object* v_unused_3785_; 
v_unused_3785_ = lean_ctor_get(v___x_3777_, 0);
lean_dec(v_unused_3785_);
v___x_3779_ = v___x_3777_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_dec(v___x_3777_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 0, v___x_3772_);
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3772_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
else
{
lean_object* v_a_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
lean_dec_ref(v___x_3772_);
v_a_3786_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3788_ = v___x_3777_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_a_3786_);
lean_dec(v___x_3777_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
else
{
lean_object* v___x_3794_; 
v___x_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3772_);
return v___x_3794_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_){
_start:
{
lean_object* v_res_3799_; 
v_res_3799_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_3795_, v_a_3796_, v_a_3797_);
lean_dec(v_a_3797_);
lean_dec_ref(v_a_3796_);
lean_dec(v_attrName_3795_);
return v_res_3799_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_3800_; 
v___x_3800_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_3801_, lean_object* v_x_3802_){
_start:
{
if (lean_obj_tag(v_x_3802_) == 0)
{
return v_x_3801_;
}
else
{
lean_object* v_key_3803_; lean_object* v_value_3804_; lean_object* v_tail_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3831_; 
v_key_3803_ = lean_ctor_get(v_x_3802_, 0);
v_value_3804_ = lean_ctor_get(v_x_3802_, 1);
v_tail_3805_ = lean_ctor_get(v_x_3802_, 2);
v_isSharedCheck_3831_ = !lean_is_exclusive(v_x_3802_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3807_ = v_x_3802_;
v_isShared_3808_ = v_isSharedCheck_3831_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_tail_3805_);
lean_inc(v_value_3804_);
lean_inc(v_key_3803_);
lean_dec(v_x_3802_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3831_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3809_; uint64_t v___y_3811_; 
v___x_3809_ = lean_array_get_size(v_x_3801_);
if (lean_obj_tag(v_key_3803_) == 0)
{
uint64_t v___x_3829_; 
v___x_3829_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_3811_ = v___x_3829_;
goto v___jp_3810_;
}
else
{
uint64_t v_hash_3830_; 
v_hash_3830_ = lean_ctor_get_uint64(v_key_3803_, sizeof(void*)*2);
v___y_3811_ = v_hash_3830_;
goto v___jp_3810_;
}
v___jp_3810_:
{
uint64_t v___x_3812_; uint64_t v___x_3813_; uint64_t v_fold_3814_; uint64_t v___x_3815_; uint64_t v___x_3816_; uint64_t v___x_3817_; size_t v___x_3818_; size_t v___x_3819_; size_t v___x_3820_; size_t v___x_3821_; size_t v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3825_; 
v___x_3812_ = 32ULL;
v___x_3813_ = lean_uint64_shift_right(v___y_3811_, v___x_3812_);
v_fold_3814_ = lean_uint64_xor(v___y_3811_, v___x_3813_);
v___x_3815_ = 16ULL;
v___x_3816_ = lean_uint64_shift_right(v_fold_3814_, v___x_3815_);
v___x_3817_ = lean_uint64_xor(v_fold_3814_, v___x_3816_);
v___x_3818_ = lean_uint64_to_usize(v___x_3817_);
v___x_3819_ = lean_usize_of_nat(v___x_3809_);
v___x_3820_ = ((size_t)1ULL);
v___x_3821_ = lean_usize_sub(v___x_3819_, v___x_3820_);
v___x_3822_ = lean_usize_land(v___x_3818_, v___x_3821_);
v___x_3823_ = lean_array_uget_borrowed(v_x_3801_, v___x_3822_);
lean_inc(v___x_3823_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 2, v___x_3823_);
v___x_3825_ = v___x_3807_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_key_3803_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v_value_3804_);
lean_ctor_set(v_reuseFailAlloc_3828_, 2, v___x_3823_);
v___x_3825_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; 
v___x_3826_ = lean_array_uset(v_x_3801_, v___x_3822_, v___x_3825_);
v_x_3801_ = v___x_3826_;
v_x_3802_ = v_tail_3805_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3832_, lean_object* v_source_3833_, lean_object* v_target_3834_){
_start:
{
lean_object* v___x_3835_; uint8_t v___x_3836_; 
v___x_3835_ = lean_array_get_size(v_source_3833_);
v___x_3836_ = lean_nat_dec_lt(v_i_3832_, v___x_3835_);
if (v___x_3836_ == 0)
{
lean_dec_ref(v_source_3833_);
lean_dec(v_i_3832_);
return v_target_3834_;
}
else
{
lean_object* v_es_3837_; lean_object* v___x_3838_; lean_object* v_source_3839_; lean_object* v_target_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; 
v_es_3837_ = lean_array_fget(v_source_3833_, v_i_3832_);
v___x_3838_ = lean_box(0);
v_source_3839_ = lean_array_fset(v_source_3833_, v_i_3832_, v___x_3838_);
v_target_3840_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3834_, v_es_3837_);
v___x_3841_ = lean_unsigned_to_nat(1u);
v___x_3842_ = lean_nat_add(v_i_3832_, v___x_3841_);
lean_dec(v_i_3832_);
v_i_3832_ = v___x_3842_;
v_source_3833_ = v_source_3839_;
v_target_3834_ = v_target_3840_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_3844_){
_start:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v_nbuckets_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3845_ = lean_array_get_size(v_data_3844_);
v___x_3846_ = lean_unsigned_to_nat(2u);
v_nbuckets_3847_ = lean_nat_mul(v___x_3845_, v___x_3846_);
v___x_3848_ = lean_unsigned_to_nat(0u);
v___x_3849_ = lean_box(0);
v___x_3850_ = lean_mk_array(v_nbuckets_3847_, v___x_3849_);
v___x_3851_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_3848_, v_data_3844_, v___x_3850_);
return v___x_3851_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_3852_, lean_object* v_x_3853_){
_start:
{
if (lean_obj_tag(v_x_3853_) == 0)
{
uint8_t v___x_3854_; 
v___x_3854_ = 0;
return v___x_3854_;
}
else
{
lean_object* v_key_3855_; lean_object* v_tail_3856_; uint8_t v___x_3857_; 
v_key_3855_ = lean_ctor_get(v_x_3853_, 0);
v_tail_3856_ = lean_ctor_get(v_x_3853_, 2);
v___x_3857_ = lean_name_eq(v_key_3855_, v_a_3852_);
if (v___x_3857_ == 0)
{
v_x_3853_ = v_tail_3856_;
goto _start;
}
else
{
return v___x_3857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_3859_, lean_object* v_x_3860_){
_start:
{
uint8_t v_res_3861_; lean_object* v_r_3862_; 
v_res_3861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3859_, v_x_3860_);
lean_dec(v_x_3860_);
lean_dec(v_a_3859_);
v_r_3862_ = lean_box(v_res_3861_);
return v_r_3862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_3863_, lean_object* v_b_3864_, lean_object* v_x_3865_){
_start:
{
if (lean_obj_tag(v_x_3865_) == 0)
{
lean_dec(v_b_3864_);
lean_dec(v_a_3863_);
return v_x_3865_;
}
else
{
lean_object* v_key_3866_; lean_object* v_value_3867_; lean_object* v_tail_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3880_; 
v_key_3866_ = lean_ctor_get(v_x_3865_, 0);
v_value_3867_ = lean_ctor_get(v_x_3865_, 1);
v_tail_3868_ = lean_ctor_get(v_x_3865_, 2);
v_isSharedCheck_3880_ = !lean_is_exclusive(v_x_3865_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3870_ = v_x_3865_;
v_isShared_3871_ = v_isSharedCheck_3880_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_tail_3868_);
lean_inc(v_value_3867_);
lean_inc(v_key_3866_);
lean_dec(v_x_3865_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3880_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
uint8_t v___x_3872_; 
v___x_3872_ = lean_name_eq(v_key_3866_, v_a_3863_);
if (v___x_3872_ == 0)
{
lean_object* v___x_3873_; lean_object* v___x_3875_; 
v___x_3873_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3863_, v_b_3864_, v_tail_3868_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 2, v___x_3873_);
v___x_3875_ = v___x_3870_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_key_3866_);
lean_ctor_set(v_reuseFailAlloc_3876_, 1, v_value_3867_);
lean_ctor_set(v_reuseFailAlloc_3876_, 2, v___x_3873_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
else
{
lean_object* v___x_3878_; 
lean_dec(v_value_3867_);
lean_dec(v_key_3866_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 1, v_b_3864_);
lean_ctor_set(v___x_3870_, 0, v_a_3863_);
v___x_3878_ = v___x_3870_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3863_);
lean_ctor_set(v_reuseFailAlloc_3879_, 1, v_b_3864_);
lean_ctor_set(v_reuseFailAlloc_3879_, 2, v_tail_3868_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_3881_, lean_object* v_a_3882_, lean_object* v_b_3883_){
_start:
{
lean_object* v_size_3884_; lean_object* v_buckets_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3931_; 
v_size_3884_ = lean_ctor_get(v_m_3881_, 0);
v_buckets_3885_ = lean_ctor_get(v_m_3881_, 1);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_m_3881_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3887_ = v_m_3881_;
v_isShared_3888_ = v_isSharedCheck_3931_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_buckets_3885_);
lean_inc(v_size_3884_);
lean_dec(v_m_3881_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3931_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3889_; uint64_t v___y_3891_; 
v___x_3889_ = lean_array_get_size(v_buckets_3885_);
if (lean_obj_tag(v_a_3882_) == 0)
{
uint64_t v___x_3929_; 
v___x_3929_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_3891_ = v___x_3929_;
goto v___jp_3890_;
}
else
{
uint64_t v_hash_3930_; 
v_hash_3930_ = lean_ctor_get_uint64(v_a_3882_, sizeof(void*)*2);
v___y_3891_ = v_hash_3930_;
goto v___jp_3890_;
}
v___jp_3890_:
{
uint64_t v___x_3892_; uint64_t v___x_3893_; uint64_t v_fold_3894_; uint64_t v___x_3895_; uint64_t v___x_3896_; uint64_t v___x_3897_; size_t v___x_3898_; size_t v___x_3899_; size_t v___x_3900_; size_t v___x_3901_; size_t v___x_3902_; lean_object* v_bkt_3903_; uint8_t v___x_3904_; 
v___x_3892_ = 32ULL;
v___x_3893_ = lean_uint64_shift_right(v___y_3891_, v___x_3892_);
v_fold_3894_ = lean_uint64_xor(v___y_3891_, v___x_3893_);
v___x_3895_ = 16ULL;
v___x_3896_ = lean_uint64_shift_right(v_fold_3894_, v___x_3895_);
v___x_3897_ = lean_uint64_xor(v_fold_3894_, v___x_3896_);
v___x_3898_ = lean_uint64_to_usize(v___x_3897_);
v___x_3899_ = lean_usize_of_nat(v___x_3889_);
v___x_3900_ = ((size_t)1ULL);
v___x_3901_ = lean_usize_sub(v___x_3899_, v___x_3900_);
v___x_3902_ = lean_usize_land(v___x_3898_, v___x_3901_);
v_bkt_3903_ = lean_array_uget_borrowed(v_buckets_3885_, v___x_3902_);
v___x_3904_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3882_, v_bkt_3903_);
if (v___x_3904_ == 0)
{
lean_object* v___x_3905_; lean_object* v_size_x27_3906_; lean_object* v___x_3907_; lean_object* v_buckets_x27_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; uint8_t v___x_3914_; 
v___x_3905_ = lean_unsigned_to_nat(1u);
v_size_x27_3906_ = lean_nat_add(v_size_3884_, v___x_3905_);
lean_dec(v_size_3884_);
lean_inc(v_bkt_3903_);
v___x_3907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3907_, 0, v_a_3882_);
lean_ctor_set(v___x_3907_, 1, v_b_3883_);
lean_ctor_set(v___x_3907_, 2, v_bkt_3903_);
v_buckets_x27_3908_ = lean_array_uset(v_buckets_3885_, v___x_3902_, v___x_3907_);
v___x_3909_ = lean_unsigned_to_nat(4u);
v___x_3910_ = lean_nat_mul(v_size_x27_3906_, v___x_3909_);
v___x_3911_ = lean_unsigned_to_nat(3u);
v___x_3912_ = lean_nat_div(v___x_3910_, v___x_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_array_get_size(v_buckets_x27_3908_);
v___x_3914_ = lean_nat_dec_le(v___x_3912_, v___x_3913_);
lean_dec(v___x_3912_);
if (v___x_3914_ == 0)
{
lean_object* v_val_3915_; lean_object* v___x_3917_; 
v_val_3915_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_3908_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 1, v_val_3915_);
lean_ctor_set(v___x_3887_, 0, v_size_x27_3906_);
v___x_3917_ = v___x_3887_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_size_x27_3906_);
lean_ctor_set(v_reuseFailAlloc_3918_, 1, v_val_3915_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
else
{
lean_object* v___x_3920_; 
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 1, v_buckets_x27_3908_);
lean_ctor_set(v___x_3887_, 0, v_size_x27_3906_);
v___x_3920_ = v___x_3887_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_size_x27_3906_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v_buckets_x27_3908_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
else
{
lean_object* v___x_3922_; lean_object* v_buckets_x27_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3927_; 
lean_inc(v_bkt_3903_);
v___x_3922_ = lean_box(0);
v_buckets_x27_3923_ = lean_array_uset(v_buckets_3885_, v___x_3902_, v___x_3922_);
v___x_3924_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3882_, v_b_3883_, v_bkt_3903_);
v___x_3925_ = lean_array_uset(v_buckets_x27_3923_, v___x_3902_, v___x_3924_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 1, v___x_3925_);
v___x_3927_ = v___x_3887_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_size_3884_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v___x_3925_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_3932_, lean_object* v_ref_3933_){
_start:
{
lean_object* v___x_3935_; 
lean_inc(v_ref_3933_);
v___x_3935_ = l_Lean_Meta_Grind_mkExtension(v_ref_3933_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; uint8_t v___x_3937_; uint8_t v___x_3938_; lean_object* v___x_3939_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc_n(v_a_3936_, 2);
lean_dec_ref(v___x_3935_);
v___x_3937_ = 0;
v___x_3938_ = 1;
lean_inc(v_ref_3933_);
lean_inc(v_attrName_3932_);
v___x_3939_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3932_, v___x_3937_, v___x_3938_, v_a_3936_, v_ref_3933_);
if (lean_obj_tag(v___x_3939_) == 0)
{
lean_object* v___x_3940_; 
lean_dec_ref(v___x_3939_);
lean_inc(v_ref_3933_);
lean_inc(v_a_3936_);
lean_inc(v_attrName_3932_);
v___x_3940_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3932_, v___x_3937_, v___x_3937_, v_a_3936_, v_ref_3933_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v___x_3941_; 
lean_dec_ref(v___x_3940_);
lean_inc(v_ref_3933_);
lean_inc(v_a_3936_);
lean_inc(v_attrName_3932_);
v___x_3941_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3932_, v___x_3938_, v___x_3938_, v_a_3936_, v_ref_3933_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v___x_3942_; 
lean_dec_ref(v___x_3941_);
lean_inc(v_a_3936_);
lean_inc(v_attrName_3932_);
v___x_3942_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3932_, v___x_3938_, v___x_3937_, v_a_3936_, v_ref_3933_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3953_; 
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3953_ == 0)
{
lean_object* v_unused_3954_; 
v_unused_3954_ = lean_ctor_get(v___x_3942_, 0);
lean_dec(v_unused_3954_);
v___x_3944_ = v___x_3942_;
v_isShared_3945_ = v_isSharedCheck_3953_;
goto v_resetjp_3943_;
}
else
{
lean_dec(v___x_3942_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3953_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3951_; 
v___x_3946_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3947_ = lean_st_ref_take(v___x_3946_);
lean_inc(v_a_3936_);
v___x_3948_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_3947_, v_attrName_3932_, v_a_3936_);
v___x_3949_ = lean_st_ref_set(v___x_3946_, v___x_3948_);
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 0, v_a_3936_);
v___x_3951_ = v___x_3944_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3936_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_dec(v_a_3936_);
lean_dec(v_attrName_3932_);
v_a_3955_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3942_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3942_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_dec(v_a_3936_);
lean_dec(v_ref_3933_);
lean_dec(v_attrName_3932_);
v_a_3963_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3941_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3941_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
lean_dec(v_a_3936_);
lean_dec(v_ref_3933_);
lean_dec(v_attrName_3932_);
v_a_3971_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3940_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3940_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
else
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3986_; 
lean_dec(v_a_3936_);
lean_dec(v_ref_3933_);
lean_dec(v_attrName_3932_);
v_a_3979_ = lean_ctor_get(v___x_3939_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3939_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3981_ = v___x_3939_;
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3939_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3984_; 
if (v_isShared_3982_ == 0)
{
v___x_3984_ = v___x_3981_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3979_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
}
else
{
lean_dec(v_ref_3933_);
lean_dec(v_attrName_3932_);
return v___x_3935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_3987_, lean_object* v_ref_3988_, lean_object* v_a_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l_Lean_Meta_Grind_registerAttr(v_attrName_3987_, v_ref_3988_);
return v_res_3990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_3991_, lean_object* v_m_3992_, lean_object* v_a_3993_, lean_object* v_b_3994_){
_start:
{
lean_object* v___x_3995_; 
v___x_3995_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_3992_, v_a_3993_, v_b_3994_);
return v___x_3995_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_3996_, lean_object* v_a_3997_, lean_object* v_x_3998_){
_start:
{
uint8_t v___x_3999_; 
v___x_3999_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3997_, v_x_3998_);
return v___x_3999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4000_, lean_object* v_a_4001_, lean_object* v_x_4002_){
_start:
{
uint8_t v_res_4003_; lean_object* v_r_4004_; 
v_res_4003_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_4000_, v_a_4001_, v_x_4002_);
lean_dec(v_x_4002_);
lean_dec(v_a_4001_);
v_r_4004_ = lean_box(v_res_4003_);
return v_r_4004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_4005_, lean_object* v_data_4006_){
_start:
{
lean_object* v___x_4007_; 
v___x_4007_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_4006_);
return v___x_4007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_4008_, lean_object* v_a_4009_, lean_object* v_b_4010_, lean_object* v_x_4011_){
_start:
{
lean_object* v___x_4012_; 
v___x_4012_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4009_, v_b_4010_, v_x_4011_);
return v___x_4012_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4013_, lean_object* v_i_4014_, lean_object* v_source_4015_, lean_object* v_target_4016_){
_start:
{
lean_object* v___x_4017_; 
v___x_4017_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_4014_, v_source_4015_, v_target_4016_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4018_, lean_object* v_x_4019_, lean_object* v_x_4020_){
_start:
{
lean_object* v___x_4021_; 
v___x_4021_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_4019_, v_x_4020_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4028_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_4029_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_4030_ = l_Lean_Meta_Grind_registerAttr(v___x_4028_, v___x_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_4033_, lean_object* v_a_4034_){
_start:
{
lean_object* v___x_4036_; lean_object* v_env_4037_; lean_object* v___x_4038_; lean_object* v_ext_4039_; lean_object* v_toEnvExtension_4040_; lean_object* v_asyncMode_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v_casesTypes_4044_; uint8_t v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4036_ = lean_st_ref_get(v_a_4034_);
v_env_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc_ref(v_env_4037_);
lean_dec(v___x_4036_);
v___x_4038_ = l_Lean_Meta_Grind_grindExt;
v_ext_4039_ = lean_ctor_get(v___x_4038_, 1);
v_toEnvExtension_4040_ = lean_ctor_get(v_ext_4039_, 0);
v_asyncMode_4041_ = lean_ctor_get(v_toEnvExtension_4040_, 2);
v___x_4042_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4043_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4042_, v___x_4038_, v_env_4037_, v_asyncMode_4041_);
v_casesTypes_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc_ref(v_casesTypes_4044_);
lean_dec(v___x_4043_);
v___x_4045_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_4044_, v_declName_4033_);
v___x_4046_ = lean_box(v___x_4045_);
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
return v___x_4047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_){
_start:
{
lean_object* v_res_4051_; 
v_res_4051_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4048_, v_a_4049_);
lean_dec(v_a_4049_);
lean_dec(v_declName_4048_);
return v_res_4051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4052_, v_a_4054_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_4057_, v_a_4058_, v_a_4059_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
lean_dec(v_declName_4057_);
return v_res_4061_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* runtime_initialize_Lean_ExtraModUses(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_normExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_normExt);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_extensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_extensionMapRef);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_grindExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_grindExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1 = _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1);
l_Lean_Meta_Grind_registerAttr___auto__1 = _init_l_Lean_Meta_Grind_registerAttr___auto__1();
lean_mark_persistent(l_Lean_Meta_Grind_registerAttr___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Injective(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ExtAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
lean_object* initialize_Lean_ExtraModUses(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Attr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Injective(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ExtAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ExtraModUses(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Attr(builtin);
}
#ifdef __cplusplus
}
#endif
