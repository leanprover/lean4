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
lean_object* v_currNamespace_755_; lean_object* v___x_756_; lean_object* v_env_757_; lean_object* v_nextMacroScope_758_; lean_object* v_ngen_759_; lean_object* v_auxDeclNGen_760_; lean_object* v_traceState_761_; lean_object* v_messages_762_; lean_object* v_infoState_763_; lean_object* v_snapshotTasks_764_; lean_object* v_newDecls_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_777_; 
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
v_newDecls_765_ = lean_ctor_get(v___x_756_, 9);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_777_ == 0)
{
lean_object* v_unused_778_; 
v_unused_778_ = lean_ctor_get(v___x_756_, 5);
lean_dec(v_unused_778_);
v___x_767_ = v___x_756_;
v_isShared_768_ = v_isSharedCheck_777_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_newDecls_765_);
lean_inc(v_snapshotTasks_764_);
lean_inc(v_infoState_763_);
lean_inc(v_messages_762_);
lean_inc(v_traceState_761_);
lean_inc(v_auxDeclNGen_760_);
lean_inc(v_ngen_759_);
lean_inc(v_nextMacroScope_758_);
lean_inc(v_env_757_);
lean_dec(v___x_756_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_777_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
lean_inc(v_currNamespace_755_);
v___x_769_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_757_, v_ext_749_, v_b_750_, v_kind_751_, v_currNamespace_755_);
v___x_770_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 5, v___x_770_);
lean_ctor_set(v___x_767_, 0, v___x_769_);
v___x_772_ = v___x_767_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_776_, 1, v_nextMacroScope_758_);
lean_ctor_set(v_reuseFailAlloc_776_, 2, v_ngen_759_);
lean_ctor_set(v_reuseFailAlloc_776_, 3, v_auxDeclNGen_760_);
lean_ctor_set(v_reuseFailAlloc_776_, 4, v_traceState_761_);
lean_ctor_set(v_reuseFailAlloc_776_, 5, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_776_, 6, v_messages_762_);
lean_ctor_set(v_reuseFailAlloc_776_, 7, v_infoState_763_);
lean_ctor_set(v_reuseFailAlloc_776_, 8, v_snapshotTasks_764_);
lean_ctor_set(v_reuseFailAlloc_776_, 9, v_newDecls_765_);
v___x_772_ = v_reuseFailAlloc_776_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = lean_st_ref_set(v___y_753_, v___x_772_);
v___x_774_ = lean_box(0);
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
return v___x_775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_779_, lean_object* v_b_780_, lean_object* v_kind_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
uint8_t v_kind_boxed_785_; lean_object* v_res_786_; 
v_kind_boxed_785_ = lean_unbox(v_kind_781_);
v_res_786_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_779_, v_b_780_, v_kind_boxed_785_, v___y_782_, v___y_783_);
lean_dec(v___y_783_);
lean_dec_ref(v___y_782_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_787_, lean_object* v_00_u03b2_788_, lean_object* v_00_u03c3_789_, lean_object* v_ext_790_, lean_object* v_b_791_, uint8_t v_kind_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_790_, v_b_791_, v_kind_792_, v___y_793_, v___y_794_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_797_, lean_object* v_00_u03b2_798_, lean_object* v_00_u03c3_799_, lean_object* v_ext_800_, lean_object* v_b_801_, lean_object* v_kind_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
uint8_t v_kind_boxed_806_; lean_object* v_res_807_; 
v_kind_boxed_806_ = lean_unbox(v_kind_802_);
v_res_807_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_797_, v_00_u03b2_798_, v_00_u03c3_799_, v_ext_800_, v_b_801_, v_kind_boxed_806_, v___y_803_, v___y_804_);
lean_dec(v___y_804_);
lean_dec_ref(v___y_803_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_808_, lean_object* v_declName_809_, uint8_t v_eager_810_, uint8_t v_attrKind_811_, lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___x_815_; 
lean_inc(v_declName_809_);
v___x_815_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_809_, v_eager_810_, v_a_812_, v_a_813_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v___x_816_; lean_object* v___x_817_; 
lean_dec_ref(v___x_815_);
v___x_816_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_816_, 0, v_declName_809_);
lean_ctor_set_uint8(v___x_816_, sizeof(void*)*1, v_eager_810_);
v___x_817_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_808_, v___x_816_, v_attrKind_811_, v_a_812_, v_a_813_);
return v___x_817_;
}
else
{
lean_dec(v_declName_809_);
lean_dec_ref(v_ext_808_);
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_818_, lean_object* v_declName_819_, lean_object* v_eager_820_, lean_object* v_attrKind_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_){
_start:
{
uint8_t v_eager_boxed_825_; uint8_t v_attrKind_boxed_826_; lean_object* v_res_827_; 
v_eager_boxed_825_ = lean_unbox(v_eager_820_);
v_attrKind_boxed_826_ = lean_unbox(v_attrKind_821_);
v_res_827_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_818_, v_declName_819_, v_eager_boxed_825_, v_attrKind_boxed_826_, v_a_822_, v_a_823_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_828_, lean_object* v_declName_829_, uint8_t v_attrKind_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___x_834_; 
lean_inc(v_declName_829_);
v___x_834_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_829_, v_a_831_, v_a_832_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_842_; 
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_842_ == 0)
{
lean_object* v_unused_843_; 
v_unused_843_ = lean_ctor_get(v___x_834_, 0);
lean_dec(v_unused_843_);
v___x_836_ = v___x_834_;
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
else
{
lean_dec(v___x_834_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_842_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_839_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 0, v_declName_829_);
v___x_839_ = v___x_836_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_declName_829_);
v___x_839_ = v_reuseFailAlloc_841_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_828_, v___x_839_, v_attrKind_830_, v_a_831_, v_a_832_);
return v___x_840_;
}
}
}
else
{
lean_dec(v_declName_829_);
lean_dec_ref(v_ext_828_);
return v___x_834_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_844_, lean_object* v_declName_845_, lean_object* v_attrKind_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
uint8_t v_attrKind_boxed_850_; lean_object* v_res_851_; 
v_attrKind_boxed_850_ = lean_unbox(v_attrKind_846_);
v_res_851_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_844_, v_declName_845_, v_attrKind_boxed_850_, v_a_847_, v_a_848_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_852_, lean_object* v_declName_853_, uint8_t v_attrKind_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v_declName_853_);
v___x_859_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_852_, v___x_858_, v_attrKind_854_, v_a_855_, v_a_856_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_860_, lean_object* v_declName_861_, lean_object* v_attrKind_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
uint8_t v_attrKind_boxed_866_; lean_object* v_res_867_; 
v_attrKind_boxed_866_ = lean_unbox(v_attrKind_862_);
v_res_867_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_860_, v_declName_861_, v_attrKind_boxed_866_, v_a_863_, v_a_864_);
lean_dec(v_a_864_);
lean_dec_ref(v_a_863_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_868_, lean_object* v_s_869_){
_start:
{
lean_object* v_casesTypes_870_; lean_object* v_funCC_871_; lean_object* v_ematch_872_; lean_object* v_inj_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
v_casesTypes_870_ = lean_ctor_get(v_s_869_, 0);
v_funCC_871_ = lean_ctor_get(v_s_869_, 2);
v_ematch_872_ = lean_ctor_get(v_s_869_, 3);
v_inj_873_ = lean_ctor_get(v_s_869_, 4);
v_isSharedCheck_880_ = !lean_is_exclusive(v_s_869_);
if (v_isSharedCheck_880_ == 0)
{
lean_object* v_unused_881_; 
v_unused_881_ = lean_ctor_get(v_s_869_, 1);
lean_dec(v_unused_881_);
v___x_875_ = v_s_869_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_inj_873_);
lean_inc(v_ematch_872_);
lean_inc(v_funCC_871_);
lean_inc(v_casesTypes_870_);
lean_dec(v_s_869_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v_a_868_);
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_casesTypes_870_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_a_868_);
lean_ctor_set(v_reuseFailAlloc_879_, 2, v_funCC_871_);
lean_ctor_set(v_reuseFailAlloc_879_, 3, v_ematch_872_);
lean_ctor_set(v_reuseFailAlloc_879_, 4, v_inj_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_882_, lean_object* v_declName_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v___x_887_; lean_object* v_ext_888_; lean_object* v_toEnvExtension_889_; lean_object* v_env_890_; lean_object* v_asyncMode_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v_extThms_894_; lean_object* v___x_895_; 
v___x_887_ = lean_st_ref_get(v_a_885_);
v_ext_888_ = lean_ctor_get(v_ext_882_, 1);
v_toEnvExtension_889_ = lean_ctor_get(v_ext_888_, 0);
v_env_890_ = lean_ctor_get(v___x_887_, 0);
lean_inc_ref(v_env_890_);
lean_dec(v___x_887_);
v_asyncMode_891_ = lean_ctor_get(v_toEnvExtension_889_, 2);
v___x_892_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_893_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_892_, v_ext_882_, v_env_890_, v_asyncMode_891_);
v_extThms_894_ = lean_ctor_get(v___x_893_, 1);
lean_inc_ref(v_extThms_894_);
lean_dec(v___x_893_);
v___x_895_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_894_, v_declName_883_, v_a_884_, v_a_885_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_926_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_926_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_926_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_926_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_900_; lean_object* v_env_901_; lean_object* v_nextMacroScope_902_; lean_object* v_ngen_903_; lean_object* v_auxDeclNGen_904_; lean_object* v_traceState_905_; lean_object* v_messages_906_; lean_object* v_infoState_907_; lean_object* v_snapshotTasks_908_; lean_object* v_newDecls_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_924_; 
v___x_900_ = lean_st_ref_take(v_a_885_);
v_env_901_ = lean_ctor_get(v___x_900_, 0);
v_nextMacroScope_902_ = lean_ctor_get(v___x_900_, 1);
v_ngen_903_ = lean_ctor_get(v___x_900_, 2);
v_auxDeclNGen_904_ = lean_ctor_get(v___x_900_, 3);
v_traceState_905_ = lean_ctor_get(v___x_900_, 4);
v_messages_906_ = lean_ctor_get(v___x_900_, 6);
v_infoState_907_ = lean_ctor_get(v___x_900_, 7);
v_snapshotTasks_908_ = lean_ctor_get(v___x_900_, 8);
v_newDecls_909_ = lean_ctor_get(v___x_900_, 9);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_924_ == 0)
{
lean_object* v_unused_925_; 
v_unused_925_ = lean_ctor_get(v___x_900_, 5);
lean_dec(v_unused_925_);
v___x_911_ = v___x_900_;
v_isShared_912_ = v_isSharedCheck_924_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_newDecls_909_);
lean_inc(v_snapshotTasks_908_);
lean_inc(v_infoState_907_);
lean_inc(v_messages_906_);
lean_inc(v_traceState_905_);
lean_inc(v_auxDeclNGen_904_);
lean_inc(v_ngen_903_);
lean_inc(v_nextMacroScope_902_);
lean_inc(v_env_901_);
lean_dec(v___x_900_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_924_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___f_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_917_; 
v___f_913_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_913_, 0, v_a_896_);
v___x_914_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_882_, v_env_901_, v___f_913_);
v___x_915_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 5, v___x_915_);
lean_ctor_set(v___x_911_, 0, v___x_914_);
v___x_917_ = v___x_911_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_nextMacroScope_902_);
lean_ctor_set(v_reuseFailAlloc_923_, 2, v_ngen_903_);
lean_ctor_set(v_reuseFailAlloc_923_, 3, v_auxDeclNGen_904_);
lean_ctor_set(v_reuseFailAlloc_923_, 4, v_traceState_905_);
lean_ctor_set(v_reuseFailAlloc_923_, 5, v___x_915_);
lean_ctor_set(v_reuseFailAlloc_923_, 6, v_messages_906_);
lean_ctor_set(v_reuseFailAlloc_923_, 7, v_infoState_907_);
lean_ctor_set(v_reuseFailAlloc_923_, 8, v_snapshotTasks_908_);
lean_ctor_set(v_reuseFailAlloc_923_, 9, v_newDecls_909_);
v___x_917_ = v_reuseFailAlloc_923_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_918_ = lean_st_ref_set(v_a_885_, v___x_917_);
v___x_919_ = lean_box(0);
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 0, v___x_919_);
v___x_921_ = v___x_898_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v_ext_882_);
v_a_927_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_895_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_895_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_935_, lean_object* v_declName_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_935_, v_declName_936_, v_a_937_, v_a_938_);
lean_dec(v_a_938_);
lean_dec_ref(v_a_937_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_941_, lean_object* v_s_942_){
_start:
{
lean_object* v_extThms_943_; lean_object* v_funCC_944_; lean_object* v_ematch_945_; lean_object* v_inj_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
v_extThms_943_ = lean_ctor_get(v_s_942_, 1);
v_funCC_944_ = lean_ctor_get(v_s_942_, 2);
v_ematch_945_ = lean_ctor_get(v_s_942_, 3);
v_inj_946_ = lean_ctor_get(v_s_942_, 4);
v_isSharedCheck_953_ = !lean_is_exclusive(v_s_942_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v_s_942_, 0);
lean_dec(v_unused_954_);
v___x_948_ = v_s_942_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_inj_946_);
lean_inc(v_ematch_945_);
lean_inc(v_funCC_944_);
lean_inc(v_extThms_943_);
lean_dec(v_s_942_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v_a_941_);
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_941_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_extThms_943_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_funCC_944_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v_ematch_945_);
lean_ctor_set(v_reuseFailAlloc_952_, 4, v_inj_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_955_, lean_object* v_declName_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_960_; 
lean_inc(v_declName_956_);
v___x_960_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_956_, v_a_957_, v_a_958_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v___x_961_; lean_object* v_ext_962_; lean_object* v_toEnvExtension_963_; lean_object* v_env_964_; lean_object* v_asyncMode_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v_casesTypes_968_; lean_object* v___x_969_; 
lean_dec_ref(v___x_960_);
v___x_961_ = lean_st_ref_get(v_a_958_);
v_ext_962_ = lean_ctor_get(v_ext_955_, 1);
v_toEnvExtension_963_ = lean_ctor_get(v_ext_962_, 0);
v_env_964_ = lean_ctor_get(v___x_961_, 0);
lean_inc_ref(v_env_964_);
lean_dec(v___x_961_);
v_asyncMode_965_ = lean_ctor_get(v_toEnvExtension_963_, 2);
v___x_966_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_967_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_966_, v_ext_955_, v_env_964_, v_asyncMode_965_);
v_casesTypes_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc_ref(v_casesTypes_968_);
lean_dec(v___x_967_);
v___x_969_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_968_, v_declName_956_, v_a_957_, v_a_958_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_1000_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_1000_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_1000_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v_env_975_; lean_object* v_nextMacroScope_976_; lean_object* v_ngen_977_; lean_object* v_auxDeclNGen_978_; lean_object* v_traceState_979_; lean_object* v_messages_980_; lean_object* v_infoState_981_; lean_object* v_snapshotTasks_982_; lean_object* v_newDecls_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_998_; 
v___x_974_ = lean_st_ref_take(v_a_958_);
v_env_975_ = lean_ctor_get(v___x_974_, 0);
v_nextMacroScope_976_ = lean_ctor_get(v___x_974_, 1);
v_ngen_977_ = lean_ctor_get(v___x_974_, 2);
v_auxDeclNGen_978_ = lean_ctor_get(v___x_974_, 3);
v_traceState_979_ = lean_ctor_get(v___x_974_, 4);
v_messages_980_ = lean_ctor_get(v___x_974_, 6);
v_infoState_981_ = lean_ctor_get(v___x_974_, 7);
v_snapshotTasks_982_ = lean_ctor_get(v___x_974_, 8);
v_newDecls_983_ = lean_ctor_get(v___x_974_, 9);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; 
v_unused_999_ = lean_ctor_get(v___x_974_, 5);
lean_dec(v_unused_999_);
v___x_985_ = v___x_974_;
v_isShared_986_ = v_isSharedCheck_998_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_newDecls_983_);
lean_inc(v_snapshotTasks_982_);
lean_inc(v_infoState_981_);
lean_inc(v_messages_980_);
lean_inc(v_traceState_979_);
lean_inc(v_auxDeclNGen_978_);
lean_inc(v_ngen_977_);
lean_inc(v_nextMacroScope_976_);
lean_inc(v_env_975_);
lean_dec(v___x_974_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_998_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___f_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_991_; 
v___f_987_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_987_, 0, v_a_970_);
v___x_988_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_955_, v_env_975_, v___f_987_);
v___x_989_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 5, v___x_989_);
lean_ctor_set(v___x_985_, 0, v___x_988_);
v___x_991_ = v___x_985_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_988_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_nextMacroScope_976_);
lean_ctor_set(v_reuseFailAlloc_997_, 2, v_ngen_977_);
lean_ctor_set(v_reuseFailAlloc_997_, 3, v_auxDeclNGen_978_);
lean_ctor_set(v_reuseFailAlloc_997_, 4, v_traceState_979_);
lean_ctor_set(v_reuseFailAlloc_997_, 5, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_997_, 6, v_messages_980_);
lean_ctor_set(v_reuseFailAlloc_997_, 7, v_infoState_981_);
lean_ctor_set(v_reuseFailAlloc_997_, 8, v_snapshotTasks_982_);
lean_ctor_set(v_reuseFailAlloc_997_, 9, v_newDecls_983_);
v___x_991_ = v_reuseFailAlloc_997_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_992_ = lean_st_ref_set(v_a_958_, v___x_991_);
v___x_993_ = lean_box(0);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_993_);
v___x_995_ = v___x_972_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_dec_ref(v_ext_955_);
v_a_1001_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_969_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_969_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
else
{
lean_dec(v_declName_956_);
lean_dec_ref(v_ext_955_);
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_1009_, lean_object* v_declName_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_1009_, v_declName_1010_, v_a_1011_, v_a_1012_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_1015_, lean_object* v_s_1016_){
_start:
{
lean_object* v_casesTypes_1017_; lean_object* v_extThms_1018_; lean_object* v_ematch_1019_; lean_object* v_inj_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1027_; 
v_casesTypes_1017_ = lean_ctor_get(v_s_1016_, 0);
v_extThms_1018_ = lean_ctor_get(v_s_1016_, 1);
v_ematch_1019_ = lean_ctor_get(v_s_1016_, 3);
v_inj_1020_ = lean_ctor_get(v_s_1016_, 4);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_s_1016_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; 
v_unused_1028_ = lean_ctor_get(v_s_1016_, 2);
lean_dec(v_unused_1028_);
v___x_1022_ = v_s_1016_;
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_inj_1020_);
lean_inc(v_ematch_1019_);
lean_inc(v_extThms_1018_);
lean_inc(v_casesTypes_1017_);
lean_dec(v_s_1016_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1027_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1025_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 2, v___x_1015_);
v___x_1025_ = v___x_1022_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_casesTypes_1017_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_extThms_1018_);
lean_ctor_set(v_reuseFailAlloc_1026_, 2, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1026_, 3, v_ematch_1019_);
lean_ctor_set(v_reuseFailAlloc_1026_, 4, v_inj_1020_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_1029_, lean_object* v_t_1030_){
_start:
{
if (lean_obj_tag(v_t_1030_) == 0)
{
lean_object* v_k_1031_; lean_object* v_v_1032_; lean_object* v_l_1033_; lean_object* v_r_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1688_; 
v_k_1031_ = lean_ctor_get(v_t_1030_, 1);
v_v_1032_ = lean_ctor_get(v_t_1030_, 2);
v_l_1033_ = lean_ctor_get(v_t_1030_, 3);
v_r_1034_ = lean_ctor_get(v_t_1030_, 4);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_t_1030_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; 
v_unused_1689_ = lean_ctor_get(v_t_1030_, 0);
lean_dec(v_unused_1689_);
v___x_1036_ = v_t_1030_;
v_isShared_1037_ = v_isSharedCheck_1688_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_r_1034_);
lean_inc(v_l_1033_);
lean_inc(v_v_1032_);
lean_inc(v_k_1031_);
lean_dec(v_t_1030_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1688_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
uint8_t v___x_1038_; 
v___x_1038_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1029_, v_k_1031_);
switch(v___x_1038_)
{
case 0:
{
lean_object* v_impl_1039_; lean_object* v___x_1040_; 
v_impl_1039_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1029_, v_l_1033_);
v___x_1040_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1039_) == 0)
{
if (lean_obj_tag(v_r_1034_) == 0)
{
lean_object* v_size_1041_; lean_object* v_size_1042_; lean_object* v_k_1043_; lean_object* v_v_1044_; lean_object* v_l_1045_; lean_object* v_r_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v_size_1041_ = lean_ctor_get(v_impl_1039_, 0);
lean_inc(v_size_1041_);
v_size_1042_ = lean_ctor_get(v_r_1034_, 0);
v_k_1043_ = lean_ctor_get(v_r_1034_, 1);
v_v_1044_ = lean_ctor_get(v_r_1034_, 2);
v_l_1045_ = lean_ctor_get(v_r_1034_, 3);
lean_inc(v_l_1045_);
v_r_1046_ = lean_ctor_get(v_r_1034_, 4);
v___x_1047_ = lean_unsigned_to_nat(3u);
v___x_1048_ = lean_nat_mul(v___x_1047_, v_size_1041_);
v___x_1049_ = lean_nat_dec_lt(v___x_1048_, v_size_1042_);
lean_dec(v___x_1048_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
lean_dec(v_l_1045_);
v___x_1050_ = lean_nat_add(v___x_1040_, v_size_1041_);
lean_dec(v_size_1041_);
v___x_1051_ = lean_nat_add(v___x_1050_, v_size_1042_);
lean_dec(v___x_1050_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 3, v_impl_1039_);
lean_ctor_set(v___x_1036_, 0, v___x_1051_);
v___x_1053_ = v___x_1036_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1054_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1054_, 3, v_impl_1039_);
lean_ctor_set(v_reuseFailAlloc_1054_, 4, v_r_1034_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
else
{
lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1118_; 
lean_inc(v_r_1046_);
lean_inc(v_v_1044_);
lean_inc(v_k_1043_);
lean_inc(v_size_1042_);
v_isSharedCheck_1118_ = !lean_is_exclusive(v_r_1034_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; lean_object* v_unused_1120_; lean_object* v_unused_1121_; lean_object* v_unused_1122_; lean_object* v_unused_1123_; 
v_unused_1119_ = lean_ctor_get(v_r_1034_, 4);
lean_dec(v_unused_1119_);
v_unused_1120_ = lean_ctor_get(v_r_1034_, 3);
lean_dec(v_unused_1120_);
v_unused_1121_ = lean_ctor_get(v_r_1034_, 2);
lean_dec(v_unused_1121_);
v_unused_1122_ = lean_ctor_get(v_r_1034_, 1);
lean_dec(v_unused_1122_);
v_unused_1123_ = lean_ctor_get(v_r_1034_, 0);
lean_dec(v_unused_1123_);
v___x_1056_ = v_r_1034_;
v_isShared_1057_ = v_isSharedCheck_1118_;
goto v_resetjp_1055_;
}
else
{
lean_dec(v_r_1034_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1118_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v_size_1058_; lean_object* v_k_1059_; lean_object* v_v_1060_; lean_object* v_l_1061_; lean_object* v_r_1062_; lean_object* v_size_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_size_1058_ = lean_ctor_get(v_l_1045_, 0);
v_k_1059_ = lean_ctor_get(v_l_1045_, 1);
v_v_1060_ = lean_ctor_get(v_l_1045_, 2);
v_l_1061_ = lean_ctor_get(v_l_1045_, 3);
v_r_1062_ = lean_ctor_get(v_l_1045_, 4);
v_size_1063_ = lean_ctor_get(v_r_1046_, 0);
v___x_1064_ = lean_unsigned_to_nat(2u);
v___x_1065_ = lean_nat_mul(v___x_1064_, v_size_1063_);
v___x_1066_ = lean_nat_dec_lt(v_size_1058_, v___x_1065_);
lean_dec(v___x_1065_);
if (v___x_1066_ == 0)
{
lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1094_; 
lean_inc(v_r_1062_);
lean_inc(v_l_1061_);
lean_inc(v_v_1060_);
lean_inc(v_k_1059_);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_l_1045_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; lean_object* v_unused_1096_; lean_object* v_unused_1097_; lean_object* v_unused_1098_; lean_object* v_unused_1099_; 
v_unused_1095_ = lean_ctor_get(v_l_1045_, 4);
lean_dec(v_unused_1095_);
v_unused_1096_ = lean_ctor_get(v_l_1045_, 3);
lean_dec(v_unused_1096_);
v_unused_1097_ = lean_ctor_get(v_l_1045_, 2);
lean_dec(v_unused_1097_);
v_unused_1098_ = lean_ctor_get(v_l_1045_, 1);
lean_dec(v_unused_1098_);
v_unused_1099_ = lean_ctor_get(v_l_1045_, 0);
lean_dec(v_unused_1099_);
v___x_1068_ = v_l_1045_;
v_isShared_1069_ = v_isSharedCheck_1094_;
goto v_resetjp_1067_;
}
else
{
lean_dec(v_l_1045_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1094_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___y_1073_; lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1084_; 
v___x_1070_ = lean_nat_add(v___x_1040_, v_size_1041_);
lean_dec(v_size_1041_);
v___x_1071_ = lean_nat_add(v___x_1070_, v_size_1042_);
lean_dec(v_size_1042_);
if (lean_obj_tag(v_l_1061_) == 0)
{
lean_object* v_size_1092_; 
v_size_1092_ = lean_ctor_get(v_l_1061_, 0);
lean_inc(v_size_1092_);
v___y_1084_ = v_size_1092_;
goto v___jp_1083_;
}
else
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_unsigned_to_nat(0u);
v___y_1084_ = v___x_1093_;
goto v___jp_1083_;
}
v___jp_1072_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1076_ = lean_nat_add(v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec(v___y_1074_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 4, v_r_1046_);
lean_ctor_set(v___x_1068_, 3, v_r_1062_);
lean_ctor_set(v___x_1068_, 2, v_v_1044_);
lean_ctor_set(v___x_1068_, 1, v_k_1043_);
lean_ctor_set(v___x_1068_, 0, v___x_1076_);
v___x_1078_ = v___x_1068_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_k_1043_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_v_1044_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v_r_1062_);
lean_ctor_set(v_reuseFailAlloc_1082_, 4, v_r_1046_);
v___x_1078_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1080_; 
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 4, v___x_1078_);
lean_ctor_set(v___x_1056_, 3, v___y_1073_);
lean_ctor_set(v___x_1056_, 2, v_v_1060_);
lean_ctor_set(v___x_1056_, 1, v_k_1059_);
lean_ctor_set(v___x_1056_, 0, v___x_1071_);
v___x_1080_ = v___x_1056_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1071_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_k_1059_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v_v_1060_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v___y_1073_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
v___jp_1083_:
{
lean_object* v___x_1085_; lean_object* v___x_1087_; 
v___x_1085_ = lean_nat_add(v___x_1070_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec(v___x_1070_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v_l_1061_);
lean_ctor_set(v___x_1036_, 3, v_impl_1039_);
lean_ctor_set(v___x_1036_, 0, v___x_1085_);
v___x_1087_ = v___x_1036_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1091_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1091_, 3, v_impl_1039_);
lean_ctor_set(v_reuseFailAlloc_1091_, 4, v_l_1061_);
v___x_1087_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1088_; 
v___x_1088_ = lean_nat_add(v___x_1040_, v_size_1063_);
if (lean_obj_tag(v_r_1062_) == 0)
{
lean_object* v_size_1089_; 
v_size_1089_ = lean_ctor_get(v_r_1062_, 0);
lean_inc(v_size_1089_);
v___y_1073_ = v___x_1087_;
v___y_1074_ = v___x_1088_;
v___y_1075_ = v_size_1089_;
goto v___jp_1072_;
}
else
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_unsigned_to_nat(0u);
v___y_1073_ = v___x_1087_;
v___y_1074_ = v___x_1088_;
v___y_1075_ = v___x_1090_;
goto v___jp_1072_;
}
}
}
}
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
lean_del_object(v___x_1036_);
v___x_1100_ = lean_nat_add(v___x_1040_, v_size_1041_);
lean_dec(v_size_1041_);
v___x_1101_ = lean_nat_add(v___x_1100_, v_size_1042_);
lean_dec(v_size_1042_);
v___x_1102_ = lean_nat_add(v___x_1100_, v_size_1058_);
lean_dec(v___x_1100_);
lean_inc_ref(v_impl_1039_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 4, v_l_1045_);
lean_ctor_set(v___x_1056_, 3, v_impl_1039_);
lean_ctor_set(v___x_1056_, 2, v_v_1032_);
lean_ctor_set(v___x_1056_, 1, v_k_1031_);
lean_ctor_set(v___x_1056_, 0, v___x_1102_);
v___x_1104_ = v___x_1056_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1117_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1117_, 3, v_impl_1039_);
lean_ctor_set(v_reuseFailAlloc_1117_, 4, v_l_1045_);
v___x_1104_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
v_isSharedCheck_1111_ = !lean_is_exclusive(v_impl_1039_);
if (v_isSharedCheck_1111_ == 0)
{
lean_object* v_unused_1112_; lean_object* v_unused_1113_; lean_object* v_unused_1114_; lean_object* v_unused_1115_; lean_object* v_unused_1116_; 
v_unused_1112_ = lean_ctor_get(v_impl_1039_, 4);
lean_dec(v_unused_1112_);
v_unused_1113_ = lean_ctor_get(v_impl_1039_, 3);
lean_dec(v_unused_1113_);
v_unused_1114_ = lean_ctor_get(v_impl_1039_, 2);
lean_dec(v_unused_1114_);
v_unused_1115_ = lean_ctor_get(v_impl_1039_, 1);
lean_dec(v_unused_1115_);
v_unused_1116_ = lean_ctor_get(v_impl_1039_, 0);
lean_dec(v_unused_1116_);
v___x_1106_ = v_impl_1039_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_dec(v_impl_1039_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 4, v_r_1046_);
lean_ctor_set(v___x_1106_, 3, v___x_1104_);
lean_ctor_set(v___x_1106_, 2, v_v_1044_);
lean_ctor_set(v___x_1106_, 1, v_k_1043_);
lean_ctor_set(v___x_1106_, 0, v___x_1101_);
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_k_1043_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_v_1044_);
lean_ctor_set(v_reuseFailAlloc_1110_, 3, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1110_, 4, v_r_1046_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1124_; lean_object* v___x_1125_; lean_object* v___x_1127_; 
v_size_1124_ = lean_ctor_get(v_impl_1039_, 0);
lean_inc(v_size_1124_);
v___x_1125_ = lean_nat_add(v___x_1040_, v_size_1124_);
lean_dec(v_size_1124_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 3, v_impl_1039_);
lean_ctor_set(v___x_1036_, 0, v___x_1125_);
v___x_1127_ = v___x_1036_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1128_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1128_, 3, v_impl_1039_);
lean_ctor_set(v_reuseFailAlloc_1128_, 4, v_r_1034_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
else
{
if (lean_obj_tag(v_r_1034_) == 0)
{
lean_object* v_l_1129_; 
v_l_1129_ = lean_ctor_get(v_r_1034_, 3);
lean_inc(v_l_1129_);
if (lean_obj_tag(v_l_1129_) == 0)
{
lean_object* v_r_1130_; 
v_r_1130_ = lean_ctor_get(v_r_1034_, 4);
lean_inc(v_r_1130_);
if (lean_obj_tag(v_r_1130_) == 0)
{
lean_object* v_size_1131_; lean_object* v_k_1132_; lean_object* v_v_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1146_; 
v_size_1131_ = lean_ctor_get(v_r_1034_, 0);
v_k_1132_ = lean_ctor_get(v_r_1034_, 1);
v_v_1133_ = lean_ctor_get(v_r_1034_, 2);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_r_1034_);
if (v_isSharedCheck_1146_ == 0)
{
lean_object* v_unused_1147_; lean_object* v_unused_1148_; 
v_unused_1147_ = lean_ctor_get(v_r_1034_, 4);
lean_dec(v_unused_1147_);
v_unused_1148_ = lean_ctor_get(v_r_1034_, 3);
lean_dec(v_unused_1148_);
v___x_1135_ = v_r_1034_;
v_isShared_1136_ = v_isSharedCheck_1146_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_v_1133_);
lean_inc(v_k_1132_);
lean_inc(v_size_1131_);
lean_dec(v_r_1034_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1146_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v_size_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1141_; 
v_size_1137_ = lean_ctor_get(v_l_1129_, 0);
v___x_1138_ = lean_nat_add(v___x_1040_, v_size_1131_);
lean_dec(v_size_1131_);
v___x_1139_ = lean_nat_add(v___x_1040_, v_size_1137_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 4, v_l_1129_);
lean_ctor_set(v___x_1135_, 3, v_impl_1039_);
lean_ctor_set(v___x_1135_, 2, v_v_1032_);
lean_ctor_set(v___x_1135_, 1, v_k_1031_);
lean_ctor_set(v___x_1135_, 0, v___x_1139_);
v___x_1141_ = v___x_1135_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1139_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1145_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1145_, 3, v_impl_1039_);
lean_ctor_set(v_reuseFailAlloc_1145_, 4, v_l_1129_);
v___x_1141_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1143_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v_r_1130_);
lean_ctor_set(v___x_1036_, 3, v___x_1141_);
lean_ctor_set(v___x_1036_, 2, v_v_1133_);
lean_ctor_set(v___x_1036_, 1, v_k_1132_);
lean_ctor_set(v___x_1036_, 0, v___x_1138_);
v___x_1143_ = v___x_1036_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_k_1132_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v_v_1133_);
lean_ctor_set(v_reuseFailAlloc_1144_, 3, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1144_, 4, v_r_1130_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
else
{
lean_object* v_k_1149_; lean_object* v_v_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1173_; 
v_k_1149_ = lean_ctor_get(v_r_1034_, 1);
v_v_1150_ = lean_ctor_get(v_r_1034_, 2);
v_isSharedCheck_1173_ = !lean_is_exclusive(v_r_1034_);
if (v_isSharedCheck_1173_ == 0)
{
lean_object* v_unused_1174_; lean_object* v_unused_1175_; lean_object* v_unused_1176_; 
v_unused_1174_ = lean_ctor_get(v_r_1034_, 4);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_r_1034_, 3);
lean_dec(v_unused_1175_);
v_unused_1176_ = lean_ctor_get(v_r_1034_, 0);
lean_dec(v_unused_1176_);
v___x_1152_ = v_r_1034_;
v_isShared_1153_ = v_isSharedCheck_1173_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_v_1150_);
lean_inc(v_k_1149_);
lean_dec(v_r_1034_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1173_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_k_1154_; lean_object* v_v_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1169_; 
v_k_1154_ = lean_ctor_get(v_l_1129_, 1);
v_v_1155_ = lean_ctor_get(v_l_1129_, 2);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_l_1129_);
if (v_isSharedCheck_1169_ == 0)
{
lean_object* v_unused_1170_; lean_object* v_unused_1171_; lean_object* v_unused_1172_; 
v_unused_1170_ = lean_ctor_get(v_l_1129_, 4);
lean_dec(v_unused_1170_);
v_unused_1171_ = lean_ctor_get(v_l_1129_, 3);
lean_dec(v_unused_1171_);
v_unused_1172_ = lean_ctor_get(v_l_1129_, 0);
lean_dec(v_unused_1172_);
v___x_1157_ = v_l_1129_;
v_isShared_1158_ = v_isSharedCheck_1169_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_v_1155_);
lean_inc(v_k_1154_);
lean_dec(v_l_1129_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1169_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1159_; lean_object* v___x_1161_; 
v___x_1159_ = lean_unsigned_to_nat(3u);
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 4, v_r_1130_);
lean_ctor_set(v___x_1157_, 3, v_r_1130_);
lean_ctor_set(v___x_1157_, 2, v_v_1032_);
lean_ctor_set(v___x_1157_, 1, v_k_1031_);
lean_ctor_set(v___x_1157_, 0, v___x_1040_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1168_, 3, v_r_1130_);
lean_ctor_set(v_reuseFailAlloc_1168_, 4, v_r_1130_);
v___x_1161_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1163_; 
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 3, v_r_1130_);
lean_ctor_set(v___x_1152_, 0, v___x_1040_);
v___x_1163_ = v___x_1152_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_k_1149_);
lean_ctor_set(v_reuseFailAlloc_1167_, 2, v_v_1150_);
lean_ctor_set(v_reuseFailAlloc_1167_, 3, v_r_1130_);
lean_ctor_set(v_reuseFailAlloc_1167_, 4, v_r_1130_);
v___x_1163_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
lean_object* v___x_1165_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1163_);
lean_ctor_set(v___x_1036_, 3, v___x_1161_);
lean_ctor_set(v___x_1036_, 2, v_v_1155_);
lean_ctor_set(v___x_1036_, 1, v_k_1154_);
lean_ctor_set(v___x_1036_, 0, v___x_1159_);
v___x_1165_ = v___x_1036_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_k_1154_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v_v_1155_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1166_, 4, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1177_; 
v_r_1177_ = lean_ctor_get(v_r_1034_, 4);
lean_inc(v_r_1177_);
if (lean_obj_tag(v_r_1177_) == 0)
{
lean_object* v_k_1178_; lean_object* v_v_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1190_; 
v_k_1178_ = lean_ctor_get(v_r_1034_, 1);
v_v_1179_ = lean_ctor_get(v_r_1034_, 2);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_r_1034_);
if (v_isSharedCheck_1190_ == 0)
{
lean_object* v_unused_1191_; lean_object* v_unused_1192_; lean_object* v_unused_1193_; 
v_unused_1191_ = lean_ctor_get(v_r_1034_, 4);
lean_dec(v_unused_1191_);
v_unused_1192_ = lean_ctor_get(v_r_1034_, 3);
lean_dec(v_unused_1192_);
v_unused_1193_ = lean_ctor_get(v_r_1034_, 0);
lean_dec(v_unused_1193_);
v___x_1181_ = v_r_1034_;
v_isShared_1182_ = v_isSharedCheck_1190_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_v_1179_);
lean_inc(v_k_1178_);
lean_dec(v_r_1034_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1190_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v___x_1183_; lean_object* v___x_1185_; 
v___x_1183_ = lean_unsigned_to_nat(3u);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 4, v_l_1129_);
lean_ctor_set(v___x_1181_, 2, v_v_1032_);
lean_ctor_set(v___x_1181_, 1, v_k_1031_);
lean_ctor_set(v___x_1181_, 0, v___x_1040_);
v___x_1185_ = v___x_1181_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v_l_1129_);
lean_ctor_set(v_reuseFailAlloc_1189_, 4, v_l_1129_);
v___x_1185_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1187_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v_r_1177_);
lean_ctor_set(v___x_1036_, 3, v___x_1185_);
lean_ctor_set(v___x_1036_, 2, v_v_1179_);
lean_ctor_set(v___x_1036_, 1, v_k_1178_);
lean_ctor_set(v___x_1036_, 0, v___x_1183_);
v___x_1187_ = v___x_1036_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1183_);
lean_ctor_set(v_reuseFailAlloc_1188_, 1, v_k_1178_);
lean_ctor_set(v_reuseFailAlloc_1188_, 2, v_v_1179_);
lean_ctor_set(v_reuseFailAlloc_1188_, 3, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1188_, 4, v_r_1177_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
else
{
lean_object* v_size_1194_; lean_object* v_k_1195_; lean_object* v_v_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1207_; 
v_size_1194_ = lean_ctor_get(v_r_1034_, 0);
v_k_1195_ = lean_ctor_get(v_r_1034_, 1);
v_v_1196_ = lean_ctor_get(v_r_1034_, 2);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_r_1034_);
if (v_isSharedCheck_1207_ == 0)
{
lean_object* v_unused_1208_; lean_object* v_unused_1209_; 
v_unused_1208_ = lean_ctor_get(v_r_1034_, 4);
lean_dec(v_unused_1208_);
v_unused_1209_ = lean_ctor_get(v_r_1034_, 3);
lean_dec(v_unused_1209_);
v___x_1198_ = v_r_1034_;
v_isShared_1199_ = v_isSharedCheck_1207_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_v_1196_);
lean_inc(v_k_1195_);
lean_inc(v_size_1194_);
lean_dec(v_r_1034_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1207_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 3, v_r_1177_);
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_size_1194_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_k_1195_);
lean_ctor_set(v_reuseFailAlloc_1206_, 2, v_v_1196_);
lean_ctor_set(v_reuseFailAlloc_1206_, 3, v_r_1177_);
lean_ctor_set(v_reuseFailAlloc_1206_, 4, v_r_1177_);
v___x_1201_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1202_ = lean_unsigned_to_nat(2u);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1201_);
lean_ctor_set(v___x_1036_, 3, v_r_1177_);
lean_ctor_set(v___x_1036_, 0, v___x_1202_);
v___x_1204_ = v___x_1036_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1205_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1205_, 3, v_r_1177_);
lean_ctor_set(v_reuseFailAlloc_1205_, 4, v___x_1201_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
}
}
else
{
lean_object* v___x_1211_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 3, v_r_1034_);
lean_ctor_set(v___x_1036_, 0, v___x_1040_);
v___x_1211_ = v___x_1036_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1040_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1212_, 3, v_r_1034_);
lean_ctor_set(v_reuseFailAlloc_1212_, 4, v_r_1034_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1036_);
lean_dec(v_v_1032_);
lean_dec(v_k_1031_);
if (lean_obj_tag(v_l_1033_) == 0)
{
if (lean_obj_tag(v_r_1034_) == 0)
{
lean_object* v_size_1213_; lean_object* v_k_1214_; lean_object* v_v_1215_; lean_object* v_l_1216_; lean_object* v_r_1217_; lean_object* v_size_1218_; lean_object* v_k_1219_; lean_object* v_v_1220_; lean_object* v_l_1221_; lean_object* v_r_1222_; lean_object* v___x_1223_; uint8_t v___x_1224_; 
v_size_1213_ = lean_ctor_get(v_l_1033_, 0);
v_k_1214_ = lean_ctor_get(v_l_1033_, 1);
v_v_1215_ = lean_ctor_get(v_l_1033_, 2);
v_l_1216_ = lean_ctor_get(v_l_1033_, 3);
v_r_1217_ = lean_ctor_get(v_l_1033_, 4);
lean_inc(v_r_1217_);
v_size_1218_ = lean_ctor_get(v_r_1034_, 0);
v_k_1219_ = lean_ctor_get(v_r_1034_, 1);
v_v_1220_ = lean_ctor_get(v_r_1034_, 2);
v_l_1221_ = lean_ctor_get(v_r_1034_, 3);
lean_inc(v_l_1221_);
v_r_1222_ = lean_ctor_get(v_r_1034_, 4);
v___x_1223_ = lean_unsigned_to_nat(1u);
v___x_1224_ = lean_nat_dec_lt(v_size_1213_, v_size_1218_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1360_; 
lean_inc(v_l_1216_);
lean_inc(v_v_1215_);
lean_inc(v_k_1214_);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_l_1033_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; lean_object* v_unused_1362_; lean_object* v_unused_1363_; lean_object* v_unused_1364_; lean_object* v_unused_1365_; 
v_unused_1361_ = lean_ctor_get(v_l_1033_, 4);
lean_dec(v_unused_1361_);
v_unused_1362_ = lean_ctor_get(v_l_1033_, 3);
lean_dec(v_unused_1362_);
v_unused_1363_ = lean_ctor_get(v_l_1033_, 2);
lean_dec(v_unused_1363_);
v_unused_1364_ = lean_ctor_get(v_l_1033_, 1);
lean_dec(v_unused_1364_);
v_unused_1365_ = lean_ctor_get(v_l_1033_, 0);
lean_dec(v_unused_1365_);
v___x_1226_ = v_l_1033_;
v_isShared_1227_ = v_isSharedCheck_1360_;
goto v_resetjp_1225_;
}
else
{
lean_dec(v_l_1033_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1360_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1228_; lean_object* v_tree_1229_; 
v___x_1228_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1214_, v_v_1215_, v_l_1216_, v_r_1217_);
v_tree_1229_ = lean_ctor_get(v___x_1228_, 2);
lean_inc(v_tree_1229_);
if (lean_obj_tag(v_tree_1229_) == 0)
{
lean_object* v_k_1230_; lean_object* v_v_1231_; lean_object* v_size_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; uint8_t v___x_1235_; 
v_k_1230_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_k_1230_);
v_v_1231_ = lean_ctor_get(v___x_1228_, 1);
lean_inc(v_v_1231_);
lean_dec_ref(v___x_1228_);
v_size_1232_ = lean_ctor_get(v_tree_1229_, 0);
v___x_1233_ = lean_unsigned_to_nat(3u);
v___x_1234_ = lean_nat_mul(v___x_1233_, v_size_1232_);
v___x_1235_ = lean_nat_dec_lt(v___x_1234_, v_size_1218_);
lean_dec(v___x_1234_);
if (v___x_1235_ == 0)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
lean_dec(v_l_1221_);
v___x_1236_ = lean_nat_add(v___x_1223_, v_size_1232_);
v___x_1237_ = lean_nat_add(v___x_1236_, v_size_1218_);
lean_dec(v___x_1236_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 4, v_r_1034_);
lean_ctor_set(v___x_1226_, 3, v_tree_1229_);
lean_ctor_set(v___x_1226_, 2, v_v_1231_);
lean_ctor_set(v___x_1226_, 1, v_k_1230_);
lean_ctor_set(v___x_1226_, 0, v___x_1237_);
v___x_1239_ = v___x_1226_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_k_1230_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v_v_1231_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_tree_1229_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v_r_1034_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
else
{
lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1295_; 
lean_inc(v_r_1222_);
lean_inc(v_v_1220_);
lean_inc(v_k_1219_);
lean_inc(v_size_1218_);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_r_1034_);
if (v_isSharedCheck_1295_ == 0)
{
lean_object* v_unused_1296_; lean_object* v_unused_1297_; lean_object* v_unused_1298_; lean_object* v_unused_1299_; lean_object* v_unused_1300_; 
v_unused_1296_ = lean_ctor_get(v_r_1034_, 4);
lean_dec(v_unused_1296_);
v_unused_1297_ = lean_ctor_get(v_r_1034_, 3);
lean_dec(v_unused_1297_);
v_unused_1298_ = lean_ctor_get(v_r_1034_, 2);
lean_dec(v_unused_1298_);
v_unused_1299_ = lean_ctor_get(v_r_1034_, 1);
lean_dec(v_unused_1299_);
v_unused_1300_ = lean_ctor_get(v_r_1034_, 0);
lean_dec(v_unused_1300_);
v___x_1242_ = v_r_1034_;
v_isShared_1243_ = v_isSharedCheck_1295_;
goto v_resetjp_1241_;
}
else
{
lean_dec(v_r_1034_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1295_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_size_1244_; lean_object* v_k_1245_; lean_object* v_v_1246_; lean_object* v_l_1247_; lean_object* v_r_1248_; lean_object* v_size_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_size_1244_ = lean_ctor_get(v_l_1221_, 0);
v_k_1245_ = lean_ctor_get(v_l_1221_, 1);
v_v_1246_ = lean_ctor_get(v_l_1221_, 2);
v_l_1247_ = lean_ctor_get(v_l_1221_, 3);
v_r_1248_ = lean_ctor_get(v_l_1221_, 4);
v_size_1249_ = lean_ctor_get(v_r_1222_, 0);
v___x_1250_ = lean_unsigned_to_nat(2u);
v___x_1251_ = lean_nat_mul(v___x_1250_, v_size_1249_);
v___x_1252_ = lean_nat_dec_lt(v_size_1244_, v___x_1251_);
lean_dec(v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1280_; 
lean_inc(v_r_1248_);
lean_inc(v_l_1247_);
lean_inc(v_v_1246_);
lean_inc(v_k_1245_);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_l_1221_);
if (v_isSharedCheck_1280_ == 0)
{
lean_object* v_unused_1281_; lean_object* v_unused_1282_; lean_object* v_unused_1283_; lean_object* v_unused_1284_; lean_object* v_unused_1285_; 
v_unused_1281_ = lean_ctor_get(v_l_1221_, 4);
lean_dec(v_unused_1281_);
v_unused_1282_ = lean_ctor_get(v_l_1221_, 3);
lean_dec(v_unused_1282_);
v_unused_1283_ = lean_ctor_get(v_l_1221_, 2);
lean_dec(v_unused_1283_);
v_unused_1284_ = lean_ctor_get(v_l_1221_, 1);
lean_dec(v_unused_1284_);
v_unused_1285_ = lean_ctor_get(v_l_1221_, 0);
lean_dec(v_unused_1285_);
v___x_1254_ = v_l_1221_;
v_isShared_1255_ = v_isSharedCheck_1280_;
goto v_resetjp_1253_;
}
else
{
lean_dec(v_l_1221_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1280_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1270_; 
v___x_1256_ = lean_nat_add(v___x_1223_, v_size_1232_);
v___x_1257_ = lean_nat_add(v___x_1256_, v_size_1218_);
lean_dec(v_size_1218_);
if (lean_obj_tag(v_l_1247_) == 0)
{
lean_object* v_size_1278_; 
v_size_1278_ = lean_ctor_get(v_l_1247_, 0);
lean_inc(v_size_1278_);
v___y_1270_ = v_size_1278_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_unsigned_to_nat(0u);
v___y_1270_ = v___x_1279_;
goto v___jp_1269_;
}
v___jp_1258_:
{
lean_object* v___x_1262_; lean_object* v___x_1264_; 
v___x_1262_ = lean_nat_add(v___y_1259_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec(v___y_1259_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 4, v_r_1222_);
lean_ctor_set(v___x_1254_, 3, v_r_1248_);
lean_ctor_set(v___x_1254_, 2, v_v_1220_);
lean_ctor_set(v___x_1254_, 1, v_k_1219_);
lean_ctor_set(v___x_1254_, 0, v___x_1262_);
v___x_1264_ = v___x_1254_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1262_);
lean_ctor_set(v_reuseFailAlloc_1268_, 1, v_k_1219_);
lean_ctor_set(v_reuseFailAlloc_1268_, 2, v_v_1220_);
lean_ctor_set(v_reuseFailAlloc_1268_, 3, v_r_1248_);
lean_ctor_set(v_reuseFailAlloc_1268_, 4, v_r_1222_);
v___x_1264_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1266_; 
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 4, v___x_1264_);
lean_ctor_set(v___x_1242_, 3, v___y_1260_);
lean_ctor_set(v___x_1242_, 2, v_v_1246_);
lean_ctor_set(v___x_1242_, 1, v_k_1245_);
lean_ctor_set(v___x_1242_, 0, v___x_1257_);
v___x_1266_ = v___x_1242_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_k_1245_);
lean_ctor_set(v_reuseFailAlloc_1267_, 2, v_v_1246_);
lean_ctor_set(v_reuseFailAlloc_1267_, 3, v___y_1260_);
lean_ctor_set(v_reuseFailAlloc_1267_, 4, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
v___jp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1271_ = lean_nat_add(v___x_1256_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec(v___x_1256_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 4, v_l_1247_);
lean_ctor_set(v___x_1226_, 3, v_tree_1229_);
lean_ctor_set(v___x_1226_, 2, v_v_1231_);
lean_ctor_set(v___x_1226_, 1, v_k_1230_);
lean_ctor_set(v___x_1226_, 0, v___x_1271_);
v___x_1273_ = v___x_1226_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_k_1230_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_v_1231_);
lean_ctor_set(v_reuseFailAlloc_1277_, 3, v_tree_1229_);
lean_ctor_set(v_reuseFailAlloc_1277_, 4, v_l_1247_);
v___x_1273_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_nat_add(v___x_1223_, v_size_1249_);
if (lean_obj_tag(v_r_1248_) == 0)
{
lean_object* v_size_1275_; 
v_size_1275_ = lean_ctor_get(v_r_1248_, 0);
lean_inc(v_size_1275_);
v___y_1259_ = v___x_1274_;
v___y_1260_ = v___x_1273_;
v___y_1261_ = v_size_1275_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1276_; 
v___x_1276_ = lean_unsigned_to_nat(0u);
v___y_1259_ = v___x_1274_;
v___y_1260_ = v___x_1273_;
v___y_1261_ = v___x_1276_;
goto v___jp_1258_;
}
}
}
}
}
else
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1286_ = lean_nat_add(v___x_1223_, v_size_1232_);
v___x_1287_ = lean_nat_add(v___x_1286_, v_size_1218_);
lean_dec(v_size_1218_);
v___x_1288_ = lean_nat_add(v___x_1286_, v_size_1244_);
lean_dec(v___x_1286_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 4, v_l_1221_);
lean_ctor_set(v___x_1242_, 3, v_tree_1229_);
lean_ctor_set(v___x_1242_, 2, v_v_1231_);
lean_ctor_set(v___x_1242_, 1, v_k_1230_);
lean_ctor_set(v___x_1242_, 0, v___x_1288_);
v___x_1290_ = v___x_1242_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_k_1230_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v_v_1231_);
lean_ctor_set(v_reuseFailAlloc_1294_, 3, v_tree_1229_);
lean_ctor_set(v_reuseFailAlloc_1294_, 4, v_l_1221_);
v___x_1290_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1292_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 4, v_r_1222_);
lean_ctor_set(v___x_1226_, 3, v___x_1290_);
lean_ctor_set(v___x_1226_, 2, v_v_1220_);
lean_ctor_set(v___x_1226_, 1, v_k_1219_);
lean_ctor_set(v___x_1226_, 0, v___x_1287_);
v___x_1292_ = v___x_1226_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1287_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_k_1219_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_v_1220_);
lean_ctor_set(v_reuseFailAlloc_1293_, 3, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1293_, 4, v_r_1222_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
}
else
{
lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1354_; 
lean_inc(v_r_1222_);
lean_inc(v_v_1220_);
lean_inc(v_k_1219_);
lean_inc(v_size_1218_);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_r_1034_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; lean_object* v_unused_1356_; lean_object* v_unused_1357_; lean_object* v_unused_1358_; lean_object* v_unused_1359_; 
v_unused_1355_ = lean_ctor_get(v_r_1034_, 4);
lean_dec(v_unused_1355_);
v_unused_1356_ = lean_ctor_get(v_r_1034_, 3);
lean_dec(v_unused_1356_);
v_unused_1357_ = lean_ctor_get(v_r_1034_, 2);
lean_dec(v_unused_1357_);
v_unused_1358_ = lean_ctor_get(v_r_1034_, 1);
lean_dec(v_unused_1358_);
v_unused_1359_ = lean_ctor_get(v_r_1034_, 0);
lean_dec(v_unused_1359_);
v___x_1302_ = v_r_1034_;
v_isShared_1303_ = v_isSharedCheck_1354_;
goto v_resetjp_1301_;
}
else
{
lean_dec(v_r_1034_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1354_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
if (lean_obj_tag(v_l_1221_) == 0)
{
if (lean_obj_tag(v_r_1222_) == 0)
{
lean_object* v_k_1304_; lean_object* v_v_1305_; lean_object* v_size_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1310_; 
v_k_1304_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_k_1304_);
v_v_1305_ = lean_ctor_get(v___x_1228_, 1);
lean_inc(v_v_1305_);
lean_dec_ref(v___x_1228_);
v_size_1306_ = lean_ctor_get(v_l_1221_, 0);
v___x_1307_ = lean_nat_add(v___x_1223_, v_size_1218_);
lean_dec(v_size_1218_);
v___x_1308_ = lean_nat_add(v___x_1223_, v_size_1306_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 4, v_l_1221_);
lean_ctor_set(v___x_1302_, 3, v_tree_1229_);
lean_ctor_set(v___x_1302_, 2, v_v_1305_);
lean_ctor_set(v___x_1302_, 1, v_k_1304_);
lean_ctor_set(v___x_1302_, 0, v___x_1308_);
v___x_1310_ = v___x_1302_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1308_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_k_1304_);
lean_ctor_set(v_reuseFailAlloc_1314_, 2, v_v_1305_);
lean_ctor_set(v_reuseFailAlloc_1314_, 3, v_tree_1229_);
lean_ctor_set(v_reuseFailAlloc_1314_, 4, v_l_1221_);
v___x_1310_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
lean_object* v___x_1312_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 4, v_r_1222_);
lean_ctor_set(v___x_1226_, 3, v___x_1310_);
lean_ctor_set(v___x_1226_, 2, v_v_1220_);
lean_ctor_set(v___x_1226_, 1, v_k_1219_);
lean_ctor_set(v___x_1226_, 0, v___x_1307_);
v___x_1312_ = v___x_1226_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_k_1219_);
lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_v_1220_);
lean_ctor_set(v_reuseFailAlloc_1313_, 3, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1313_, 4, v_r_1222_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
else
{
lean_object* v_k_1315_; lean_object* v_v_1316_; lean_object* v_k_1317_; lean_object* v_v_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_size_1218_);
v_k_1315_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_k_1315_);
v_v_1316_ = lean_ctor_get(v___x_1228_, 1);
lean_inc(v_v_1316_);
lean_dec_ref(v___x_1228_);
v_k_1317_ = lean_ctor_get(v_l_1221_, 1);
v_v_1318_ = lean_ctor_get(v_l_1221_, 2);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_l_1221_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; lean_object* v_unused_1334_; lean_object* v_unused_1335_; 
v_unused_1333_ = lean_ctor_get(v_l_1221_, 4);
lean_dec(v_unused_1333_);
v_unused_1334_ = lean_ctor_get(v_l_1221_, 3);
lean_dec(v_unused_1334_);
v_unused_1335_ = lean_ctor_get(v_l_1221_, 0);
lean_dec(v_unused_1335_);
v___x_1320_ = v_l_1221_;
v_isShared_1321_ = v_isSharedCheck_1332_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_v_1318_);
lean_inc(v_k_1317_);
lean_dec(v_l_1221_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1332_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1322_; lean_object* v___x_1324_; 
v___x_1322_ = lean_unsigned_to_nat(3u);
if (v_isShared_1321_ == 0)
{
lean_ctor_set(v___x_1320_, 4, v_r_1222_);
lean_ctor_set(v___x_1320_, 3, v_r_1222_);
lean_ctor_set(v___x_1320_, 2, v_v_1316_);
lean_ctor_set(v___x_1320_, 1, v_k_1315_);
lean_ctor_set(v___x_1320_, 0, v___x_1223_);
v___x_1324_ = v___x_1320_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_k_1315_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_v_1316_);
lean_ctor_set(v_reuseFailAlloc_1331_, 3, v_r_1222_);
lean_ctor_set(v_reuseFailAlloc_1331_, 4, v_r_1222_);
v___x_1324_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v___x_1326_; 
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 3, v_r_1222_);
lean_ctor_set(v___x_1302_, 0, v___x_1223_);
v___x_1326_ = v___x_1302_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_k_1219_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_v_1220_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v_r_1222_);
lean_ctor_set(v_reuseFailAlloc_1330_, 4, v_r_1222_);
v___x_1326_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1328_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 4, v___x_1326_);
lean_ctor_set(v___x_1226_, 3, v___x_1324_);
lean_ctor_set(v___x_1226_, 2, v_v_1318_);
lean_ctor_set(v___x_1226_, 1, v_k_1317_);
lean_ctor_set(v___x_1226_, 0, v___x_1322_);
v___x_1328_ = v___x_1226_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1322_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_k_1317_);
lean_ctor_set(v_reuseFailAlloc_1329_, 2, v_v_1318_);
lean_ctor_set(v_reuseFailAlloc_1329_, 3, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1329_, 4, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1222_) == 0)
{
lean_object* v_k_1336_; lean_object* v_v_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
lean_dec(v_size_1218_);
v_k_1336_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_k_1336_);
v_v_1337_ = lean_ctor_get(v___x_1228_, 1);
lean_inc(v_v_1337_);
lean_dec_ref(v___x_1228_);
v___x_1338_ = lean_unsigned_to_nat(3u);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 4, v_l_1221_);
lean_ctor_set(v___x_1302_, 2, v_v_1337_);
lean_ctor_set(v___x_1302_, 1, v_k_1336_);
lean_ctor_set(v___x_1302_, 0, v___x_1223_);
v___x_1340_ = v___x_1302_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_k_1336_);
lean_ctor_set(v_reuseFailAlloc_1344_, 2, v_v_1337_);
lean_ctor_set(v_reuseFailAlloc_1344_, 3, v_l_1221_);
lean_ctor_set(v_reuseFailAlloc_1344_, 4, v_l_1221_);
v___x_1340_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1342_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 4, v_r_1222_);
lean_ctor_set(v___x_1226_, 3, v___x_1340_);
lean_ctor_set(v___x_1226_, 2, v_v_1220_);
lean_ctor_set(v___x_1226_, 1, v_k_1219_);
lean_ctor_set(v___x_1226_, 0, v___x_1338_);
v___x_1342_ = v___x_1226_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_k_1219_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_v_1220_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v___x_1340_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v_r_1222_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
else
{
lean_object* v_k_1345_; lean_object* v_v_1346_; lean_object* v___x_1348_; 
v_k_1345_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_k_1345_);
v_v_1346_ = lean_ctor_get(v___x_1228_, 1);
lean_inc(v_v_1346_);
lean_dec_ref(v___x_1228_);
if (v_isShared_1303_ == 0)
{
lean_ctor_set(v___x_1302_, 3, v_r_1222_);
v___x_1348_ = v___x_1302_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_size_1218_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_k_1219_);
lean_ctor_set(v_reuseFailAlloc_1353_, 2, v_v_1220_);
lean_ctor_set(v_reuseFailAlloc_1353_, 3, v_r_1222_);
lean_ctor_set(v_reuseFailAlloc_1353_, 4, v_r_1222_);
v___x_1348_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_unsigned_to_nat(2u);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 4, v___x_1348_);
lean_ctor_set(v___x_1226_, 3, v_r_1222_);
lean_ctor_set(v___x_1226_, 2, v_v_1346_);
lean_ctor_set(v___x_1226_, 1, v_k_1345_);
lean_ctor_set(v___x_1226_, 0, v___x_1349_);
v___x_1351_ = v___x_1226_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_k_1345_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_v_1346_);
lean_ctor_set(v_reuseFailAlloc_1352_, 3, v_r_1222_);
lean_ctor_set(v_reuseFailAlloc_1352_, 4, v___x_1348_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
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
lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1518_; 
lean_inc(v_r_1222_);
lean_inc(v_v_1220_);
lean_inc(v_k_1219_);
v_isSharedCheck_1518_ = !lean_is_exclusive(v_r_1034_);
if (v_isSharedCheck_1518_ == 0)
{
lean_object* v_unused_1519_; lean_object* v_unused_1520_; lean_object* v_unused_1521_; lean_object* v_unused_1522_; lean_object* v_unused_1523_; 
v_unused_1519_ = lean_ctor_get(v_r_1034_, 4);
lean_dec(v_unused_1519_);
v_unused_1520_ = lean_ctor_get(v_r_1034_, 3);
lean_dec(v_unused_1520_);
v_unused_1521_ = lean_ctor_get(v_r_1034_, 2);
lean_dec(v_unused_1521_);
v_unused_1522_ = lean_ctor_get(v_r_1034_, 1);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_r_1034_, 0);
lean_dec(v_unused_1523_);
v___x_1367_ = v_r_1034_;
v_isShared_1368_ = v_isSharedCheck_1518_;
goto v_resetjp_1366_;
}
else
{
lean_dec(v_r_1034_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1518_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v_tree_1370_; 
v___x_1369_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1219_, v_v_1220_, v_l_1221_, v_r_1222_);
v_tree_1370_ = lean_ctor_get(v___x_1369_, 2);
lean_inc(v_tree_1370_);
if (lean_obj_tag(v_tree_1370_) == 0)
{
lean_object* v_k_1371_; lean_object* v_v_1372_; lean_object* v_size_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; uint8_t v___x_1376_; 
v_k_1371_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_k_1371_);
v_v_1372_ = lean_ctor_get(v___x_1369_, 1);
lean_inc(v_v_1372_);
lean_dec_ref(v___x_1369_);
v_size_1373_ = lean_ctor_get(v_tree_1370_, 0);
v___x_1374_ = lean_unsigned_to_nat(3u);
v___x_1375_ = lean_nat_mul(v___x_1374_, v_size_1373_);
v___x_1376_ = lean_nat_dec_lt(v___x_1375_, v_size_1213_);
lean_dec(v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1380_; 
lean_dec(v_r_1217_);
v___x_1377_ = lean_nat_add(v___x_1223_, v_size_1213_);
v___x_1378_ = lean_nat_add(v___x_1377_, v_size_1373_);
lean_dec(v___x_1377_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 4, v_tree_1370_);
lean_ctor_set(v___x_1367_, 3, v_l_1033_);
lean_ctor_set(v___x_1367_, 2, v_v_1372_);
lean_ctor_set(v___x_1367_, 1, v_k_1371_);
lean_ctor_set(v___x_1367_, 0, v___x_1378_);
v___x_1380_ = v___x_1367_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v___x_1378_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1381_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1381_, 3, v_l_1033_);
lean_ctor_set(v_reuseFailAlloc_1381_, 4, v_tree_1370_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
else
{
lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1447_; 
lean_inc(v_l_1216_);
lean_inc(v_v_1215_);
lean_inc(v_k_1214_);
lean_inc(v_size_1213_);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_l_1033_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; lean_object* v_unused_1449_; lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; 
v_unused_1448_ = lean_ctor_get(v_l_1033_, 4);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_l_1033_, 3);
lean_dec(v_unused_1449_);
v_unused_1450_ = lean_ctor_get(v_l_1033_, 2);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_l_1033_, 1);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_l_1033_, 0);
lean_dec(v_unused_1452_);
v___x_1383_ = v_l_1033_;
v_isShared_1384_ = v_isSharedCheck_1447_;
goto v_resetjp_1382_;
}
else
{
lean_dec(v_l_1033_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1447_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v_size_1385_; lean_object* v_size_1386_; lean_object* v_k_1387_; lean_object* v_v_1388_; lean_object* v_l_1389_; lean_object* v_r_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v_size_1385_ = lean_ctor_get(v_l_1216_, 0);
v_size_1386_ = lean_ctor_get(v_r_1217_, 0);
v_k_1387_ = lean_ctor_get(v_r_1217_, 1);
v_v_1388_ = lean_ctor_get(v_r_1217_, 2);
v_l_1389_ = lean_ctor_get(v_r_1217_, 3);
v_r_1390_ = lean_ctor_get(v_r_1217_, 4);
v___x_1391_ = lean_unsigned_to_nat(2u);
v___x_1392_ = lean_nat_mul(v___x_1391_, v_size_1385_);
v___x_1393_ = lean_nat_dec_lt(v_size_1386_, v___x_1392_);
lean_dec(v___x_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1431_; 
lean_inc(v_r_1390_);
lean_inc(v_l_1389_);
lean_inc(v_v_1388_);
lean_inc(v_k_1387_);
lean_del_object(v___x_1383_);
v_isSharedCheck_1431_ = !lean_is_exclusive(v_r_1217_);
if (v_isSharedCheck_1431_ == 0)
{
lean_object* v_unused_1432_; lean_object* v_unused_1433_; lean_object* v_unused_1434_; lean_object* v_unused_1435_; lean_object* v_unused_1436_; 
v_unused_1432_ = lean_ctor_get(v_r_1217_, 4);
lean_dec(v_unused_1432_);
v_unused_1433_ = lean_ctor_get(v_r_1217_, 3);
lean_dec(v_unused_1433_);
v_unused_1434_ = lean_ctor_get(v_r_1217_, 2);
lean_dec(v_unused_1434_);
v_unused_1435_ = lean_ctor_get(v_r_1217_, 1);
lean_dec(v_unused_1435_);
v_unused_1436_ = lean_ctor_get(v_r_1217_, 0);
lean_dec(v_unused_1436_);
v___x_1395_ = v_r_1217_;
v_isShared_1396_ = v_isSharedCheck_1431_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v_r_1217_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1431_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___x_1419_; lean_object* v___y_1421_; 
v___x_1397_ = lean_nat_add(v___x_1223_, v_size_1213_);
lean_dec(v_size_1213_);
v___x_1398_ = lean_nat_add(v___x_1397_, v_size_1373_);
lean_dec(v___x_1397_);
v___x_1419_ = lean_nat_add(v___x_1223_, v_size_1385_);
if (lean_obj_tag(v_l_1389_) == 0)
{
lean_object* v_size_1429_; 
v_size_1429_ = lean_ctor_get(v_l_1389_, 0);
lean_inc(v_size_1429_);
v___y_1421_ = v_size_1429_;
goto v___jp_1420_;
}
else
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_unsigned_to_nat(0u);
v___y_1421_ = v___x_1430_;
goto v___jp_1420_;
}
v___jp_1399_:
{
lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1403_ = lean_nat_add(v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec(v___y_1401_);
lean_inc_ref(v_tree_1370_);
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 4, v_tree_1370_);
lean_ctor_set(v___x_1395_, 3, v_r_1390_);
lean_ctor_set(v___x_1395_, 2, v_v_1372_);
lean_ctor_set(v___x_1395_, 1, v_k_1371_);
lean_ctor_set(v___x_1395_, 0, v___x_1403_);
v___x_1405_ = v___x_1395_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1418_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1418_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1418_, 3, v_r_1390_);
lean_ctor_set(v_reuseFailAlloc_1418_, 4, v_tree_1370_);
v___x_1405_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
v_isSharedCheck_1412_ = !lean_is_exclusive(v_tree_1370_);
if (v_isSharedCheck_1412_ == 0)
{
lean_object* v_unused_1413_; lean_object* v_unused_1414_; lean_object* v_unused_1415_; lean_object* v_unused_1416_; lean_object* v_unused_1417_; 
v_unused_1413_ = lean_ctor_get(v_tree_1370_, 4);
lean_dec(v_unused_1413_);
v_unused_1414_ = lean_ctor_get(v_tree_1370_, 3);
lean_dec(v_unused_1414_);
v_unused_1415_ = lean_ctor_get(v_tree_1370_, 2);
lean_dec(v_unused_1415_);
v_unused_1416_ = lean_ctor_get(v_tree_1370_, 1);
lean_dec(v_unused_1416_);
v_unused_1417_ = lean_ctor_get(v_tree_1370_, 0);
lean_dec(v_unused_1417_);
v___x_1407_ = v_tree_1370_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_dec(v_tree_1370_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
lean_ctor_set(v___x_1407_, 4, v___x_1405_);
lean_ctor_set(v___x_1407_, 3, v___y_1400_);
lean_ctor_set(v___x_1407_, 2, v_v_1388_);
lean_ctor_set(v___x_1407_, 1, v_k_1387_);
lean_ctor_set(v___x_1407_, 0, v___x_1398_);
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v___x_1398_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_k_1387_);
lean_ctor_set(v_reuseFailAlloc_1411_, 2, v_v_1388_);
lean_ctor_set(v_reuseFailAlloc_1411_, 3, v___y_1400_);
lean_ctor_set(v_reuseFailAlloc_1411_, 4, v___x_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
v___jp_1420_:
{
lean_object* v___x_1422_; lean_object* v___x_1424_; 
v___x_1422_ = lean_nat_add(v___x_1419_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec(v___x_1419_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 4, v_l_1389_);
lean_ctor_set(v___x_1367_, 3, v_l_1216_);
lean_ctor_set(v___x_1367_, 2, v_v_1215_);
lean_ctor_set(v___x_1367_, 1, v_k_1214_);
lean_ctor_set(v___x_1367_, 0, v___x_1422_);
v___x_1424_ = v___x_1367_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1422_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_k_1214_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_v_1215_);
lean_ctor_set(v_reuseFailAlloc_1428_, 3, v_l_1216_);
lean_ctor_set(v_reuseFailAlloc_1428_, 4, v_l_1389_);
v___x_1424_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_nat_add(v___x_1223_, v_size_1373_);
if (lean_obj_tag(v_r_1390_) == 0)
{
lean_object* v_size_1426_; 
v_size_1426_ = lean_ctor_get(v_r_1390_, 0);
lean_inc(v_size_1426_);
v___y_1400_ = v___x_1424_;
v___y_1401_ = v___x_1425_;
v___y_1402_ = v_size_1426_;
goto v___jp_1399_;
}
else
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_unsigned_to_nat(0u);
v___y_1400_ = v___x_1424_;
v___y_1401_ = v___x_1425_;
v___y_1402_ = v___x_1427_;
goto v___jp_1399_;
}
}
}
}
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1442_; 
v___x_1437_ = lean_nat_add(v___x_1223_, v_size_1213_);
lean_dec(v_size_1213_);
v___x_1438_ = lean_nat_add(v___x_1437_, v_size_1373_);
lean_dec(v___x_1437_);
v___x_1439_ = lean_nat_add(v___x_1223_, v_size_1373_);
v___x_1440_ = lean_nat_add(v___x_1439_, v_size_1386_);
lean_dec(v___x_1439_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 4, v_tree_1370_);
lean_ctor_set(v___x_1367_, 3, v_r_1217_);
lean_ctor_set(v___x_1367_, 2, v_v_1372_);
lean_ctor_set(v___x_1367_, 1, v_k_1371_);
lean_ctor_set(v___x_1367_, 0, v___x_1440_);
v___x_1442_ = v___x_1367_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_k_1371_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_v_1372_);
lean_ctor_set(v_reuseFailAlloc_1446_, 3, v_r_1217_);
lean_ctor_set(v_reuseFailAlloc_1446_, 4, v_tree_1370_);
v___x_1442_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1444_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v___x_1442_);
lean_ctor_set(v___x_1383_, 0, v___x_1438_);
v___x_1444_ = v___x_1383_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v_k_1214_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_v_1215_);
lean_ctor_set(v_reuseFailAlloc_1445_, 3, v_l_1216_);
lean_ctor_set(v_reuseFailAlloc_1445_, 4, v___x_1442_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1216_) == 0)
{
lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1476_; 
lean_inc_ref(v_l_1216_);
lean_inc(v_v_1215_);
lean_inc(v_k_1214_);
lean_inc(v_size_1213_);
v_isSharedCheck_1476_ = !lean_is_exclusive(v_l_1033_);
if (v_isSharedCheck_1476_ == 0)
{
lean_object* v_unused_1477_; lean_object* v_unused_1478_; lean_object* v_unused_1479_; lean_object* v_unused_1480_; lean_object* v_unused_1481_; 
v_unused_1477_ = lean_ctor_get(v_l_1033_, 4);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_l_1033_, 3);
lean_dec(v_unused_1478_);
v_unused_1479_ = lean_ctor_get(v_l_1033_, 2);
lean_dec(v_unused_1479_);
v_unused_1480_ = lean_ctor_get(v_l_1033_, 1);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_l_1033_, 0);
lean_dec(v_unused_1481_);
v___x_1454_ = v_l_1033_;
v_isShared_1455_ = v_isSharedCheck_1476_;
goto v_resetjp_1453_;
}
else
{
lean_dec(v_l_1033_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1476_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
if (lean_obj_tag(v_r_1217_) == 0)
{
lean_object* v_k_1456_; lean_object* v_v_1457_; lean_object* v_size_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v_k_1456_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_k_1456_);
v_v_1457_ = lean_ctor_get(v___x_1369_, 1);
lean_inc(v_v_1457_);
lean_dec_ref(v___x_1369_);
v_size_1458_ = lean_ctor_get(v_r_1217_, 0);
v___x_1459_ = lean_nat_add(v___x_1223_, v_size_1213_);
lean_dec(v_size_1213_);
v___x_1460_ = lean_nat_add(v___x_1223_, v_size_1458_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 4, v_tree_1370_);
lean_ctor_set(v___x_1367_, 3, v_r_1217_);
lean_ctor_set(v___x_1367_, 2, v_v_1457_);
lean_ctor_set(v___x_1367_, 1, v_k_1456_);
lean_ctor_set(v___x_1367_, 0, v___x_1460_);
v___x_1462_ = v___x_1367_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1466_, 1, v_k_1456_);
lean_ctor_set(v_reuseFailAlloc_1466_, 2, v_v_1457_);
lean_ctor_set(v_reuseFailAlloc_1466_, 3, v_r_1217_);
lean_ctor_set(v_reuseFailAlloc_1466_, 4, v_tree_1370_);
v___x_1462_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1464_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 4, v___x_1462_);
lean_ctor_set(v___x_1454_, 0, v___x_1459_);
v___x_1464_ = v___x_1454_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_k_1214_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_v_1215_);
lean_ctor_set(v_reuseFailAlloc_1465_, 3, v_l_1216_);
lean_ctor_set(v_reuseFailAlloc_1465_, 4, v___x_1462_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
else
{
lean_object* v_k_1467_; lean_object* v_v_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
lean_dec(v_size_1213_);
v_k_1467_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_k_1467_);
v_v_1468_ = lean_ctor_get(v___x_1369_, 1);
lean_inc(v_v_1468_);
lean_dec_ref(v___x_1369_);
v___x_1469_ = lean_unsigned_to_nat(3u);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 4, v_r_1217_);
lean_ctor_set(v___x_1367_, 3, v_r_1217_);
lean_ctor_set(v___x_1367_, 2, v_v_1468_);
lean_ctor_set(v___x_1367_, 1, v_k_1467_);
lean_ctor_set(v___x_1367_, 0, v___x_1223_);
v___x_1471_ = v___x_1367_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1475_, 1, v_k_1467_);
lean_ctor_set(v_reuseFailAlloc_1475_, 2, v_v_1468_);
lean_ctor_set(v_reuseFailAlloc_1475_, 3, v_r_1217_);
lean_ctor_set(v_reuseFailAlloc_1475_, 4, v_r_1217_);
v___x_1471_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
lean_object* v___x_1473_; 
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 4, v___x_1471_);
lean_ctor_set(v___x_1454_, 0, v___x_1469_);
v___x_1473_ = v___x_1454_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v_k_1214_);
lean_ctor_set(v_reuseFailAlloc_1474_, 2, v_v_1215_);
lean_ctor_set(v_reuseFailAlloc_1474_, 3, v_l_1216_);
lean_ctor_set(v_reuseFailAlloc_1474_, 4, v___x_1471_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1217_) == 0)
{
lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1506_; 
lean_inc(v_l_1216_);
lean_inc(v_v_1215_);
lean_inc(v_k_1214_);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_l_1033_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; lean_object* v_unused_1508_; lean_object* v_unused_1509_; lean_object* v_unused_1510_; lean_object* v_unused_1511_; 
v_unused_1507_ = lean_ctor_get(v_l_1033_, 4);
lean_dec(v_unused_1507_);
v_unused_1508_ = lean_ctor_get(v_l_1033_, 3);
lean_dec(v_unused_1508_);
v_unused_1509_ = lean_ctor_get(v_l_1033_, 2);
lean_dec(v_unused_1509_);
v_unused_1510_ = lean_ctor_get(v_l_1033_, 1);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_l_1033_, 0);
lean_dec(v_unused_1511_);
v___x_1483_ = v_l_1033_;
v_isShared_1484_ = v_isSharedCheck_1506_;
goto v_resetjp_1482_;
}
else
{
lean_dec(v_l_1033_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1506_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v_k_1485_; lean_object* v_v_1486_; lean_object* v_k_1487_; lean_object* v_v_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1502_; 
v_k_1485_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_k_1485_);
v_v_1486_ = lean_ctor_get(v___x_1369_, 1);
lean_inc(v_v_1486_);
lean_dec_ref(v___x_1369_);
v_k_1487_ = lean_ctor_get(v_r_1217_, 1);
v_v_1488_ = lean_ctor_get(v_r_1217_, 2);
v_isSharedCheck_1502_ = !lean_is_exclusive(v_r_1217_);
if (v_isSharedCheck_1502_ == 0)
{
lean_object* v_unused_1503_; lean_object* v_unused_1504_; lean_object* v_unused_1505_; 
v_unused_1503_ = lean_ctor_get(v_r_1217_, 4);
lean_dec(v_unused_1503_);
v_unused_1504_ = lean_ctor_get(v_r_1217_, 3);
lean_dec(v_unused_1504_);
v_unused_1505_ = lean_ctor_get(v_r_1217_, 0);
lean_dec(v_unused_1505_);
v___x_1490_ = v_r_1217_;
v_isShared_1491_ = v_isSharedCheck_1502_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_v_1488_);
lean_inc(v_k_1487_);
lean_dec(v_r_1217_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1502_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1492_ = lean_unsigned_to_nat(3u);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 4, v_l_1216_);
lean_ctor_set(v___x_1490_, 3, v_l_1216_);
lean_ctor_set(v___x_1490_, 2, v_v_1215_);
lean_ctor_set(v___x_1490_, 1, v_k_1214_);
lean_ctor_set(v___x_1490_, 0, v___x_1223_);
v___x_1494_ = v___x_1490_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1501_, 1, v_k_1214_);
lean_ctor_set(v_reuseFailAlloc_1501_, 2, v_v_1215_);
lean_ctor_set(v_reuseFailAlloc_1501_, 3, v_l_1216_);
lean_ctor_set(v_reuseFailAlloc_1501_, 4, v_l_1216_);
v___x_1494_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1496_; 
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 4, v_l_1216_);
lean_ctor_set(v___x_1367_, 3, v_l_1216_);
lean_ctor_set(v___x_1367_, 2, v_v_1486_);
lean_ctor_set(v___x_1367_, 1, v_k_1485_);
lean_ctor_set(v___x_1367_, 0, v___x_1223_);
v___x_1496_ = v___x_1367_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1223_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_k_1485_);
lean_ctor_set(v_reuseFailAlloc_1500_, 2, v_v_1486_);
lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_l_1216_);
lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_l_1216_);
v___x_1496_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
lean_object* v___x_1498_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 4, v___x_1496_);
lean_ctor_set(v___x_1483_, 3, v___x_1494_);
lean_ctor_set(v___x_1483_, 2, v_v_1488_);
lean_ctor_set(v___x_1483_, 1, v_k_1487_);
lean_ctor_set(v___x_1483_, 0, v___x_1492_);
v___x_1498_ = v___x_1483_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_k_1487_);
lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_v_1488_);
lean_ctor_set(v_reuseFailAlloc_1499_, 3, v___x_1494_);
lean_ctor_set(v_reuseFailAlloc_1499_, 4, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
}
else
{
lean_object* v_k_1512_; lean_object* v_v_1513_; lean_object* v___x_1514_; lean_object* v___x_1516_; 
v_k_1512_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_k_1512_);
v_v_1513_ = lean_ctor_get(v___x_1369_, 1);
lean_inc(v_v_1513_);
lean_dec_ref(v___x_1369_);
v___x_1514_ = lean_unsigned_to_nat(2u);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 4, v_r_1217_);
lean_ctor_set(v___x_1367_, 3, v_l_1033_);
lean_ctor_set(v___x_1367_, 2, v_v_1513_);
lean_ctor_set(v___x_1367_, 1, v_k_1512_);
lean_ctor_set(v___x_1367_, 0, v___x_1514_);
v___x_1516_ = v___x_1367_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1514_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_k_1512_);
lean_ctor_set(v_reuseFailAlloc_1517_, 2, v_v_1513_);
lean_ctor_set(v_reuseFailAlloc_1517_, 3, v_l_1033_);
lean_ctor_set(v_reuseFailAlloc_1517_, 4, v_r_1217_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
}
}
}
else
{
return v_l_1033_;
}
}
else
{
return v_r_1034_;
}
}
default: 
{
lean_object* v_impl_1524_; lean_object* v___x_1525_; 
v_impl_1524_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1029_, v_r_1034_);
v___x_1525_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1524_) == 0)
{
if (lean_obj_tag(v_l_1033_) == 0)
{
lean_object* v_size_1526_; lean_object* v_size_1527_; lean_object* v_k_1528_; lean_object* v_v_1529_; lean_object* v_l_1530_; lean_object* v_r_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v_size_1526_ = lean_ctor_get(v_impl_1524_, 0);
lean_inc(v_size_1526_);
v_size_1527_ = lean_ctor_get(v_l_1033_, 0);
v_k_1528_ = lean_ctor_get(v_l_1033_, 1);
v_v_1529_ = lean_ctor_get(v_l_1033_, 2);
v_l_1530_ = lean_ctor_get(v_l_1033_, 3);
v_r_1531_ = lean_ctor_get(v_l_1033_, 4);
lean_inc(v_r_1531_);
v___x_1532_ = lean_unsigned_to_nat(3u);
v___x_1533_ = lean_nat_mul(v___x_1532_, v_size_1526_);
v___x_1534_ = lean_nat_dec_lt(v___x_1533_, v_size_1527_);
lean_dec(v___x_1533_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
lean_dec(v_r_1531_);
v___x_1535_ = lean_nat_add(v___x_1525_, v_size_1527_);
v___x_1536_ = lean_nat_add(v___x_1535_, v_size_1526_);
lean_dec(v_size_1526_);
lean_dec(v___x_1535_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v_impl_1524_);
lean_ctor_set(v___x_1036_, 0, v___x_1536_);
v___x_1538_ = v___x_1036_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1539_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1539_, 3, v_l_1033_);
lean_ctor_set(v_reuseFailAlloc_1539_, 4, v_impl_1524_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
else
{
lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1605_; 
lean_inc(v_l_1530_);
lean_inc(v_v_1529_);
lean_inc(v_k_1528_);
lean_inc(v_size_1527_);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_l_1033_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; lean_object* v_unused_1607_; lean_object* v_unused_1608_; lean_object* v_unused_1609_; lean_object* v_unused_1610_; 
v_unused_1606_ = lean_ctor_get(v_l_1033_, 4);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_l_1033_, 3);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_l_1033_, 2);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_l_1033_, 1);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_l_1033_, 0);
lean_dec(v_unused_1610_);
v___x_1541_ = v_l_1033_;
v_isShared_1542_ = v_isSharedCheck_1605_;
goto v_resetjp_1540_;
}
else
{
lean_dec(v_l_1033_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1605_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v_size_1543_; lean_object* v_size_1544_; lean_object* v_k_1545_; lean_object* v_v_1546_; lean_object* v_l_1547_; lean_object* v_r_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; uint8_t v___x_1551_; 
v_size_1543_ = lean_ctor_get(v_l_1530_, 0);
v_size_1544_ = lean_ctor_get(v_r_1531_, 0);
v_k_1545_ = lean_ctor_get(v_r_1531_, 1);
v_v_1546_ = lean_ctor_get(v_r_1531_, 2);
v_l_1547_ = lean_ctor_get(v_r_1531_, 3);
v_r_1548_ = lean_ctor_get(v_r_1531_, 4);
v___x_1549_ = lean_unsigned_to_nat(2u);
v___x_1550_ = lean_nat_mul(v___x_1549_, v_size_1543_);
v___x_1551_ = lean_nat_dec_lt(v_size_1544_, v___x_1550_);
lean_dec(v___x_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1580_; 
lean_inc(v_r_1548_);
lean_inc(v_l_1547_);
lean_inc(v_v_1546_);
lean_inc(v_k_1545_);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_r_1531_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; lean_object* v_unused_1582_; lean_object* v_unused_1583_; lean_object* v_unused_1584_; lean_object* v_unused_1585_; 
v_unused_1581_ = lean_ctor_get(v_r_1531_, 4);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v_r_1531_, 3);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v_r_1531_, 2);
lean_dec(v_unused_1583_);
v_unused_1584_ = lean_ctor_get(v_r_1531_, 1);
lean_dec(v_unused_1584_);
v_unused_1585_ = lean_ctor_get(v_r_1531_, 0);
lean_dec(v_unused_1585_);
v___x_1553_ = v_r_1531_;
v_isShared_1554_ = v_isSharedCheck_1580_;
goto v_resetjp_1552_;
}
else
{
lean_dec(v_r_1531_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1580_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___y_1558_; lean_object* v___y_1559_; lean_object* v___y_1560_; lean_object* v___x_1568_; lean_object* v___y_1570_; 
v___x_1555_ = lean_nat_add(v___x_1525_, v_size_1527_);
lean_dec(v_size_1527_);
v___x_1556_ = lean_nat_add(v___x_1555_, v_size_1526_);
lean_dec(v___x_1555_);
v___x_1568_ = lean_nat_add(v___x_1525_, v_size_1543_);
if (lean_obj_tag(v_l_1547_) == 0)
{
lean_object* v_size_1578_; 
v_size_1578_ = lean_ctor_get(v_l_1547_, 0);
lean_inc(v_size_1578_);
v___y_1570_ = v_size_1578_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_unsigned_to_nat(0u);
v___y_1570_ = v___x_1579_;
goto v___jp_1569_;
}
v___jp_1557_:
{
lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1561_ = lean_nat_add(v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec(v___y_1559_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 4, v_impl_1524_);
lean_ctor_set(v___x_1553_, 3, v_r_1548_);
lean_ctor_set(v___x_1553_, 2, v_v_1032_);
lean_ctor_set(v___x_1553_, 1, v_k_1031_);
lean_ctor_set(v___x_1553_, 0, v___x_1561_);
v___x_1563_ = v___x_1553_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1561_);
lean_ctor_set(v_reuseFailAlloc_1567_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1567_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1567_, 3, v_r_1548_);
lean_ctor_set(v_reuseFailAlloc_1567_, 4, v_impl_1524_);
v___x_1563_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
lean_object* v___x_1565_; 
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 4, v___x_1563_);
lean_ctor_set(v___x_1541_, 3, v___y_1558_);
lean_ctor_set(v___x_1541_, 2, v_v_1546_);
lean_ctor_set(v___x_1541_, 1, v_k_1545_);
lean_ctor_set(v___x_1541_, 0, v___x_1556_);
v___x_1565_ = v___x_1541_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_k_1545_);
lean_ctor_set(v_reuseFailAlloc_1566_, 2, v_v_1546_);
lean_ctor_set(v_reuseFailAlloc_1566_, 3, v___y_1558_);
lean_ctor_set(v_reuseFailAlloc_1566_, 4, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
v___jp_1569_:
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = lean_nat_add(v___x_1568_, v___y_1570_);
lean_dec(v___y_1570_);
lean_dec(v___x_1568_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v_l_1547_);
lean_ctor_set(v___x_1036_, 3, v_l_1530_);
lean_ctor_set(v___x_1036_, 2, v_v_1529_);
lean_ctor_set(v___x_1036_, 1, v_k_1528_);
lean_ctor_set(v___x_1036_, 0, v___x_1571_);
v___x_1573_ = v___x_1036_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1571_);
lean_ctor_set(v_reuseFailAlloc_1577_, 1, v_k_1528_);
lean_ctor_set(v_reuseFailAlloc_1577_, 2, v_v_1529_);
lean_ctor_set(v_reuseFailAlloc_1577_, 3, v_l_1530_);
lean_ctor_set(v_reuseFailAlloc_1577_, 4, v_l_1547_);
v___x_1573_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_nat_add(v___x_1525_, v_size_1526_);
lean_dec(v_size_1526_);
if (lean_obj_tag(v_r_1548_) == 0)
{
lean_object* v_size_1575_; 
v_size_1575_ = lean_ctor_get(v_r_1548_, 0);
lean_inc(v_size_1575_);
v___y_1558_ = v___x_1573_;
v___y_1559_ = v___x_1574_;
v___y_1560_ = v_size_1575_;
goto v___jp_1557_;
}
else
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_unsigned_to_nat(0u);
v___y_1558_ = v___x_1573_;
v___y_1559_ = v___x_1574_;
v___y_1560_ = v___x_1576_;
goto v___jp_1557_;
}
}
}
}
}
else
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
lean_del_object(v___x_1036_);
v___x_1586_ = lean_nat_add(v___x_1525_, v_size_1527_);
lean_dec(v_size_1527_);
v___x_1587_ = lean_nat_add(v___x_1586_, v_size_1526_);
lean_dec(v___x_1586_);
v___x_1588_ = lean_nat_add(v___x_1525_, v_size_1526_);
lean_dec(v_size_1526_);
v___x_1589_ = lean_nat_add(v___x_1588_, v_size_1544_);
lean_dec(v___x_1588_);
lean_inc_ref(v_impl_1524_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 4, v_impl_1524_);
lean_ctor_set(v___x_1541_, 3, v_r_1531_);
lean_ctor_set(v___x_1541_, 2, v_v_1032_);
lean_ctor_set(v___x_1541_, 1, v_k_1031_);
lean_ctor_set(v___x_1541_, 0, v___x_1589_);
v___x_1591_ = v___x_1541_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1604_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1604_, 3, v_r_1531_);
lean_ctor_set(v_reuseFailAlloc_1604_, 4, v_impl_1524_);
v___x_1591_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1598_; 
v_isSharedCheck_1598_ = !lean_is_exclusive(v_impl_1524_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; lean_object* v_unused_1600_; lean_object* v_unused_1601_; lean_object* v_unused_1602_; lean_object* v_unused_1603_; 
v_unused_1599_ = lean_ctor_get(v_impl_1524_, 4);
lean_dec(v_unused_1599_);
v_unused_1600_ = lean_ctor_get(v_impl_1524_, 3);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_impl_1524_, 2);
lean_dec(v_unused_1601_);
v_unused_1602_ = lean_ctor_get(v_impl_1524_, 1);
lean_dec(v_unused_1602_);
v_unused_1603_ = lean_ctor_get(v_impl_1524_, 0);
lean_dec(v_unused_1603_);
v___x_1593_ = v_impl_1524_;
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
else
{
lean_dec(v_impl_1524_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1598_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1596_; 
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 4, v___x_1591_);
lean_ctor_set(v___x_1593_, 3, v_l_1530_);
lean_ctor_set(v___x_1593_, 2, v_v_1529_);
lean_ctor_set(v___x_1593_, 1, v_k_1528_);
lean_ctor_set(v___x_1593_, 0, v___x_1587_);
v___x_1596_ = v___x_1593_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1597_; 
v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1597_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_k_1528_);
lean_ctor_set(v_reuseFailAlloc_1597_, 2, v_v_1529_);
lean_ctor_set(v_reuseFailAlloc_1597_, 3, v_l_1530_);
lean_ctor_set(v_reuseFailAlloc_1597_, 4, v___x_1591_);
v___x_1596_ = v_reuseFailAlloc_1597_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
return v___x_1596_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1611_; lean_object* v___x_1612_; lean_object* v___x_1614_; 
v_size_1611_ = lean_ctor_get(v_impl_1524_, 0);
lean_inc(v_size_1611_);
v___x_1612_ = lean_nat_add(v___x_1525_, v_size_1611_);
lean_dec(v_size_1611_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v_impl_1524_);
lean_ctor_set(v___x_1036_, 0, v___x_1612_);
v___x_1614_ = v___x_1036_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1612_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1615_, 3, v_l_1033_);
lean_ctor_set(v_reuseFailAlloc_1615_, 4, v_impl_1524_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
else
{
if (lean_obj_tag(v_l_1033_) == 0)
{
lean_object* v_l_1616_; 
v_l_1616_ = lean_ctor_get(v_l_1033_, 3);
if (lean_obj_tag(v_l_1616_) == 0)
{
lean_object* v_r_1617_; 
lean_inc_ref(v_l_1616_);
v_r_1617_ = lean_ctor_get(v_l_1033_, 4);
lean_inc(v_r_1617_);
if (lean_obj_tag(v_r_1617_) == 0)
{
lean_object* v_size_1618_; lean_object* v_k_1619_; lean_object* v_v_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1633_; 
v_size_1618_ = lean_ctor_get(v_l_1033_, 0);
v_k_1619_ = lean_ctor_get(v_l_1033_, 1);
v_v_1620_ = lean_ctor_get(v_l_1033_, 2);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_l_1033_);
if (v_isSharedCheck_1633_ == 0)
{
lean_object* v_unused_1634_; lean_object* v_unused_1635_; 
v_unused_1634_ = lean_ctor_get(v_l_1033_, 4);
lean_dec(v_unused_1634_);
v_unused_1635_ = lean_ctor_get(v_l_1033_, 3);
lean_dec(v_unused_1635_);
v___x_1622_ = v_l_1033_;
v_isShared_1623_ = v_isSharedCheck_1633_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_v_1620_);
lean_inc(v_k_1619_);
lean_inc(v_size_1618_);
lean_dec(v_l_1033_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1633_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v_size_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v_size_1624_ = lean_ctor_get(v_r_1617_, 0);
v___x_1625_ = lean_nat_add(v___x_1525_, v_size_1618_);
lean_dec(v_size_1618_);
v___x_1626_ = lean_nat_add(v___x_1525_, v_size_1624_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 4, v_impl_1524_);
lean_ctor_set(v___x_1622_, 3, v_r_1617_);
lean_ctor_set(v___x_1622_, 2, v_v_1032_);
lean_ctor_set(v___x_1622_, 1, v_k_1031_);
lean_ctor_set(v___x_1622_, 0, v___x_1626_);
v___x_1628_ = v___x_1622_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1632_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1632_, 3, v_r_1617_);
lean_ctor_set(v_reuseFailAlloc_1632_, 4, v_impl_1524_);
v___x_1628_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
lean_object* v___x_1630_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1628_);
lean_ctor_set(v___x_1036_, 3, v_l_1616_);
lean_ctor_set(v___x_1036_, 2, v_v_1620_);
lean_ctor_set(v___x_1036_, 1, v_k_1619_);
lean_ctor_set(v___x_1036_, 0, v___x_1625_);
v___x_1630_ = v___x_1036_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_k_1619_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_v_1620_);
lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_l_1616_);
lean_ctor_set(v_reuseFailAlloc_1631_, 4, v___x_1628_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
else
{
lean_object* v_k_1636_; lean_object* v_v_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1648_; 
v_k_1636_ = lean_ctor_get(v_l_1033_, 1);
v_v_1637_ = lean_ctor_get(v_l_1033_, 2);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_l_1033_);
if (v_isSharedCheck_1648_ == 0)
{
lean_object* v_unused_1649_; lean_object* v_unused_1650_; lean_object* v_unused_1651_; 
v_unused_1649_ = lean_ctor_get(v_l_1033_, 4);
lean_dec(v_unused_1649_);
v_unused_1650_ = lean_ctor_get(v_l_1033_, 3);
lean_dec(v_unused_1650_);
v_unused_1651_ = lean_ctor_get(v_l_1033_, 0);
lean_dec(v_unused_1651_);
v___x_1639_ = v_l_1033_;
v_isShared_1640_ = v_isSharedCheck_1648_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_v_1637_);
lean_inc(v_k_1636_);
lean_dec(v_l_1033_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1648_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1641_ = lean_unsigned_to_nat(3u);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 3, v_r_1617_);
lean_ctor_set(v___x_1639_, 2, v_v_1032_);
lean_ctor_set(v___x_1639_, 1, v_k_1031_);
lean_ctor_set(v___x_1639_, 0, v___x_1525_);
v___x_1643_ = v___x_1639_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1647_, 3, v_r_1617_);
lean_ctor_set(v_reuseFailAlloc_1647_, 4, v_r_1617_);
v___x_1643_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
lean_object* v___x_1645_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1643_);
lean_ctor_set(v___x_1036_, 3, v_l_1616_);
lean_ctor_set(v___x_1036_, 2, v_v_1637_);
lean_ctor_set(v___x_1036_, 1, v_k_1636_);
lean_ctor_set(v___x_1036_, 0, v___x_1641_);
v___x_1645_ = v___x_1036_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v___x_1641_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_k_1636_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v_v_1637_);
lean_ctor_set(v_reuseFailAlloc_1646_, 3, v_l_1616_);
lean_ctor_set(v_reuseFailAlloc_1646_, 4, v___x_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
}
else
{
lean_object* v_r_1652_; 
v_r_1652_ = lean_ctor_get(v_l_1033_, 4);
lean_inc(v_r_1652_);
if (lean_obj_tag(v_r_1652_) == 0)
{
lean_object* v_k_1653_; lean_object* v_v_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1677_; 
lean_inc(v_l_1616_);
v_k_1653_ = lean_ctor_get(v_l_1033_, 1);
v_v_1654_ = lean_ctor_get(v_l_1033_, 2);
v_isSharedCheck_1677_ = !lean_is_exclusive(v_l_1033_);
if (v_isSharedCheck_1677_ == 0)
{
lean_object* v_unused_1678_; lean_object* v_unused_1679_; lean_object* v_unused_1680_; 
v_unused_1678_ = lean_ctor_get(v_l_1033_, 4);
lean_dec(v_unused_1678_);
v_unused_1679_ = lean_ctor_get(v_l_1033_, 3);
lean_dec(v_unused_1679_);
v_unused_1680_ = lean_ctor_get(v_l_1033_, 0);
lean_dec(v_unused_1680_);
v___x_1656_ = v_l_1033_;
v_isShared_1657_ = v_isSharedCheck_1677_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_v_1654_);
lean_inc(v_k_1653_);
lean_dec(v_l_1033_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1677_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v_k_1658_; lean_object* v_v_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1673_; 
v_k_1658_ = lean_ctor_get(v_r_1652_, 1);
v_v_1659_ = lean_ctor_get(v_r_1652_, 2);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_r_1652_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; lean_object* v_unused_1675_; lean_object* v_unused_1676_; 
v_unused_1674_ = lean_ctor_get(v_r_1652_, 4);
lean_dec(v_unused_1674_);
v_unused_1675_ = lean_ctor_get(v_r_1652_, 3);
lean_dec(v_unused_1675_);
v_unused_1676_ = lean_ctor_get(v_r_1652_, 0);
lean_dec(v_unused_1676_);
v___x_1661_ = v_r_1652_;
v_isShared_1662_ = v_isSharedCheck_1673_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_v_1659_);
lean_inc(v_k_1658_);
lean_dec(v_r_1652_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1673_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = lean_unsigned_to_nat(3u);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 4, v_l_1616_);
lean_ctor_set(v___x_1661_, 3, v_l_1616_);
lean_ctor_set(v___x_1661_, 2, v_v_1654_);
lean_ctor_set(v___x_1661_, 1, v_k_1653_);
lean_ctor_set(v___x_1661_, 0, v___x_1525_);
v___x_1665_ = v___x_1661_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_k_1653_);
lean_ctor_set(v_reuseFailAlloc_1672_, 2, v_v_1654_);
lean_ctor_set(v_reuseFailAlloc_1672_, 3, v_l_1616_);
lean_ctor_set(v_reuseFailAlloc_1672_, 4, v_l_1616_);
v___x_1665_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1667_; 
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 4, v_l_1616_);
lean_ctor_set(v___x_1656_, 2, v_v_1032_);
lean_ctor_set(v___x_1656_, 1, v_k_1031_);
lean_ctor_set(v___x_1656_, 0, v___x_1525_);
v___x_1667_ = v___x_1656_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1671_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1671_, 3, v_l_1616_);
lean_ctor_set(v_reuseFailAlloc_1671_, 4, v_l_1616_);
v___x_1667_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
lean_object* v___x_1669_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v___x_1667_);
lean_ctor_set(v___x_1036_, 3, v___x_1665_);
lean_ctor_set(v___x_1036_, 2, v_v_1659_);
lean_ctor_set(v___x_1036_, 1, v_k_1658_);
lean_ctor_set(v___x_1036_, 0, v___x_1663_);
v___x_1669_ = v___x_1036_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1670_, 1, v_k_1658_);
lean_ctor_set(v_reuseFailAlloc_1670_, 2, v_v_1659_);
lean_ctor_set(v_reuseFailAlloc_1670_, 3, v___x_1665_);
lean_ctor_set(v_reuseFailAlloc_1670_, 4, v___x_1667_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
}
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = lean_unsigned_to_nat(2u);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v_r_1652_);
lean_ctor_set(v___x_1036_, 0, v___x_1681_);
v___x_1683_ = v___x_1036_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1684_, 3, v_l_1033_);
lean_ctor_set(v_reuseFailAlloc_1684_, 4, v_r_1652_);
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
else
{
lean_object* v___x_1686_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 4, v_l_1033_);
lean_ctor_set(v___x_1036_, 0, v___x_1525_);
v___x_1686_ = v___x_1036_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_k_1031_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_v_1032_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_l_1033_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_l_1033_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
}
}
}
else
{
return v_t_1030_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_1690_, lean_object* v_t_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1690_, v_t_1691_);
lean_dec(v_k_1690_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_1693_, lean_object* v_declName_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_){
_start:
{
lean_object* v___x_1698_; lean_object* v_ext_1699_; lean_object* v_toEnvExtension_1700_; lean_object* v_env_1701_; lean_object* v_asyncMode_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___y_1706_; lean_object* v_funCC_1733_; uint8_t v___x_1734_; 
v___x_1698_ = lean_st_ref_get(v_a_1696_);
v_ext_1699_ = lean_ctor_get(v_ext_1693_, 1);
v_toEnvExtension_1700_ = lean_ctor_get(v_ext_1699_, 0);
v_env_1701_ = lean_ctor_get(v___x_1698_, 0);
lean_inc_ref(v_env_1701_);
lean_dec(v___x_1698_);
v_asyncMode_1702_ = lean_ctor_get(v_toEnvExtension_1700_, 2);
v___x_1703_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1704_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1703_, v_ext_1693_, v_env_1701_, v_asyncMode_1702_);
v_funCC_1733_ = lean_ctor_get(v___x_1704_, 2);
lean_inc(v_funCC_1733_);
v___x_1734_ = l_Lean_NameSet_contains(v_funCC_1733_, v_declName_1694_);
lean_dec(v_funCC_1733_);
if (v___x_1734_ == 0)
{
lean_object* v___x_1735_; 
lean_inc(v_declName_1694_);
v___x_1735_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_1694_, v_a_1695_, v_a_1696_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_dec_ref(v___x_1735_);
v___y_1706_ = v_a_1696_;
goto v___jp_1705_;
}
else
{
lean_dec(v___x_1704_);
lean_dec(v_declName_1694_);
lean_dec_ref(v_ext_1693_);
return v___x_1735_;
}
}
else
{
v___y_1706_ = v_a_1696_;
goto v___jp_1705_;
}
v___jp_1705_:
{
lean_object* v_funCC_1707_; lean_object* v___x_1708_; lean_object* v_env_1709_; lean_object* v_nextMacroScope_1710_; lean_object* v_ngen_1711_; lean_object* v_auxDeclNGen_1712_; lean_object* v_traceState_1713_; lean_object* v_messages_1714_; lean_object* v_infoState_1715_; lean_object* v_snapshotTasks_1716_; lean_object* v_newDecls_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1731_; 
v_funCC_1707_ = lean_ctor_get(v___x_1704_, 2);
lean_inc(v_funCC_1707_);
lean_dec(v___x_1704_);
v___x_1708_ = lean_st_ref_take(v___y_1706_);
v_env_1709_ = lean_ctor_get(v___x_1708_, 0);
v_nextMacroScope_1710_ = lean_ctor_get(v___x_1708_, 1);
v_ngen_1711_ = lean_ctor_get(v___x_1708_, 2);
v_auxDeclNGen_1712_ = lean_ctor_get(v___x_1708_, 3);
v_traceState_1713_ = lean_ctor_get(v___x_1708_, 4);
v_messages_1714_ = lean_ctor_get(v___x_1708_, 6);
v_infoState_1715_ = lean_ctor_get(v___x_1708_, 7);
v_snapshotTasks_1716_ = lean_ctor_get(v___x_1708_, 8);
v_newDecls_1717_ = lean_ctor_get(v___x_1708_, 9);
v_isSharedCheck_1731_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1731_ == 0)
{
lean_object* v_unused_1732_; 
v_unused_1732_ = lean_ctor_get(v___x_1708_, 5);
lean_dec(v_unused_1732_);
v___x_1719_ = v___x_1708_;
v_isShared_1720_ = v_isSharedCheck_1731_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_newDecls_1717_);
lean_inc(v_snapshotTasks_1716_);
lean_inc(v_infoState_1715_);
lean_inc(v_messages_1714_);
lean_inc(v_traceState_1713_);
lean_inc(v_auxDeclNGen_1712_);
lean_inc(v_ngen_1711_);
lean_inc(v_nextMacroScope_1710_);
lean_inc(v_env_1709_);
lean_dec(v___x_1708_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1731_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v___f_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1726_; 
v___x_1721_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_1694_, v_funCC_1707_);
lean_dec(v_declName_1694_);
v___f_1722_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_1722_, 0, v___x_1721_);
v___x_1723_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1693_, v_env_1709_, v___f_1722_);
v___x_1724_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 5, v___x_1724_);
lean_ctor_set(v___x_1719_, 0, v___x_1723_);
v___x_1726_ = v___x_1719_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1723_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v_nextMacroScope_1710_);
lean_ctor_set(v_reuseFailAlloc_1730_, 2, v_ngen_1711_);
lean_ctor_set(v_reuseFailAlloc_1730_, 3, v_auxDeclNGen_1712_);
lean_ctor_set(v_reuseFailAlloc_1730_, 4, v_traceState_1713_);
lean_ctor_set(v_reuseFailAlloc_1730_, 5, v___x_1724_);
lean_ctor_set(v_reuseFailAlloc_1730_, 6, v_messages_1714_);
lean_ctor_set(v_reuseFailAlloc_1730_, 7, v_infoState_1715_);
lean_ctor_set(v_reuseFailAlloc_1730_, 8, v_snapshotTasks_1716_);
lean_ctor_set(v_reuseFailAlloc_1730_, 9, v_newDecls_1717_);
v___x_1726_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v___x_1727_ = lean_st_ref_set(v___y_1706_, v___x_1726_);
v___x_1728_ = lean_box(0);
v___x_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
return v___x_1729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_1736_, lean_object* v_declName_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_1736_, v_declName_1737_, v_a_1738_, v_a_1739_);
lean_dec(v_a_1739_);
lean_dec_ref(v_a_1738_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_1742_, lean_object* v_k_1743_, lean_object* v_t_1744_, lean_object* v_h_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1743_, v_t_1744_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_1747_, lean_object* v_k_1748_, lean_object* v_t_1749_, lean_object* v_h_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_1747_, v_k_1748_, v_t_1749_, v_h_1750_);
lean_dec(v_k_1748_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_1752_, lean_object* v_s_1753_){
_start:
{
lean_object* v_casesTypes_1754_; lean_object* v_extThms_1755_; lean_object* v_funCC_1756_; lean_object* v_inj_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
v_casesTypes_1754_ = lean_ctor_get(v_s_1753_, 0);
v_extThms_1755_ = lean_ctor_get(v_s_1753_, 1);
v_funCC_1756_ = lean_ctor_get(v_s_1753_, 2);
v_inj_1757_ = lean_ctor_get(v_s_1753_, 4);
v_isSharedCheck_1764_ = !lean_is_exclusive(v_s_1753_);
if (v_isSharedCheck_1764_ == 0)
{
lean_object* v_unused_1765_; 
v_unused_1765_ = lean_ctor_get(v_s_1753_, 3);
lean_dec(v_unused_1765_);
v___x_1759_ = v_s_1753_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_inj_1757_);
lean_inc(v_funCC_1756_);
lean_inc(v_extThms_1755_);
lean_inc(v_casesTypes_1754_);
lean_dec(v_s_1753_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 3, v_a_1752_);
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_casesTypes_1754_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_extThms_1755_);
lean_ctor_set(v_reuseFailAlloc_1763_, 2, v_funCC_1756_);
lean_ctor_set(v_reuseFailAlloc_1763_, 3, v_a_1752_);
lean_ctor_set(v_reuseFailAlloc_1763_, 4, v_inj_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_1767_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
lean_ctor_set(v___x_1767_, 2, v___x_1766_);
lean_ctor_set(v___x_1767_, 3, v___x_1766_);
lean_ctor_set(v___x_1767_, 4, v___x_1766_);
lean_ctor_set(v___x_1767_, 5, v___x_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_1768_, lean_object* v_declName_1769_, lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_){
_start:
{
lean_object* v___x_1775_; lean_object* v_ext_1776_; lean_object* v_toEnvExtension_1777_; lean_object* v_env_1778_; lean_object* v_asyncMode_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v_ematch_1782_; lean_object* v___x_1783_; 
v___x_1775_ = lean_st_ref_get(v_a_1773_);
v_ext_1776_ = lean_ctor_get(v_ext_1768_, 1);
v_toEnvExtension_1777_ = lean_ctor_get(v_ext_1776_, 0);
v_env_1778_ = lean_ctor_get(v___x_1775_, 0);
lean_inc_ref(v_env_1778_);
lean_dec(v___x_1775_);
v_asyncMode_1779_ = lean_ctor_get(v_toEnvExtension_1777_, 2);
v___x_1780_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1781_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1780_, v_ext_1768_, v_env_1778_, v_asyncMode_1779_);
v_ematch_1782_ = lean_ctor_get(v___x_1781_, 3);
lean_inc_ref(v_ematch_1782_);
lean_dec(v___x_1781_);
v___x_1783_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_1782_, v_declName_1769_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1829_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1786_ = v___x_1783_;
v_isShared_1787_ = v_isSharedCheck_1829_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1829_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1788_; lean_object* v_env_1789_; lean_object* v_nextMacroScope_1790_; lean_object* v_ngen_1791_; lean_object* v_auxDeclNGen_1792_; lean_object* v_traceState_1793_; lean_object* v_messages_1794_; lean_object* v_infoState_1795_; lean_object* v_snapshotTasks_1796_; lean_object* v_newDecls_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1827_; 
v___x_1788_ = lean_st_ref_take(v_a_1773_);
v_env_1789_ = lean_ctor_get(v___x_1788_, 0);
v_nextMacroScope_1790_ = lean_ctor_get(v___x_1788_, 1);
v_ngen_1791_ = lean_ctor_get(v___x_1788_, 2);
v_auxDeclNGen_1792_ = lean_ctor_get(v___x_1788_, 3);
v_traceState_1793_ = lean_ctor_get(v___x_1788_, 4);
v_messages_1794_ = lean_ctor_get(v___x_1788_, 6);
v_infoState_1795_ = lean_ctor_get(v___x_1788_, 7);
v_snapshotTasks_1796_ = lean_ctor_get(v___x_1788_, 8);
v_newDecls_1797_ = lean_ctor_get(v___x_1788_, 9);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v___x_1788_, 5);
lean_dec(v_unused_1828_);
v___x_1799_ = v___x_1788_;
v_isShared_1800_ = v_isSharedCheck_1827_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_newDecls_1797_);
lean_inc(v_snapshotTasks_1796_);
lean_inc(v_infoState_1795_);
lean_inc(v_messages_1794_);
lean_inc(v_traceState_1793_);
lean_inc(v_auxDeclNGen_1792_);
lean_inc(v_ngen_1791_);
lean_inc(v_nextMacroScope_1790_);
lean_inc(v_env_1789_);
lean_dec(v___x_1788_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1827_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___f_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___f_1801_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_1801_, 0, v_a_1784_);
v___x_1802_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1768_, v_env_1789_, v___f_1801_);
v___x_1803_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 5, v___x_1803_);
lean_ctor_set(v___x_1799_, 0, v___x_1802_);
v___x_1805_ = v___x_1799_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_nextMacroScope_1790_);
lean_ctor_set(v_reuseFailAlloc_1826_, 2, v_ngen_1791_);
lean_ctor_set(v_reuseFailAlloc_1826_, 3, v_auxDeclNGen_1792_);
lean_ctor_set(v_reuseFailAlloc_1826_, 4, v_traceState_1793_);
lean_ctor_set(v_reuseFailAlloc_1826_, 5, v___x_1803_);
lean_ctor_set(v_reuseFailAlloc_1826_, 6, v_messages_1794_);
lean_ctor_set(v_reuseFailAlloc_1826_, 7, v_infoState_1795_);
lean_ctor_set(v_reuseFailAlloc_1826_, 8, v_snapshotTasks_1796_);
lean_ctor_set(v_reuseFailAlloc_1826_, 9, v_newDecls_1797_);
v___x_1805_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v_mctx_1808_; lean_object* v_zetaDeltaFVarIds_1809_; lean_object* v_postponed_1810_; lean_object* v_diag_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1824_; 
v___x_1806_ = lean_st_ref_set(v_a_1773_, v___x_1805_);
v___x_1807_ = lean_st_ref_take(v_a_1771_);
v_mctx_1808_ = lean_ctor_get(v___x_1807_, 0);
v_zetaDeltaFVarIds_1809_ = lean_ctor_get(v___x_1807_, 2);
v_postponed_1810_ = lean_ctor_get(v___x_1807_, 3);
v_diag_1811_ = lean_ctor_get(v___x_1807_, 4);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1824_ == 0)
{
lean_object* v_unused_1825_; 
v_unused_1825_ = lean_ctor_get(v___x_1807_, 1);
lean_dec(v_unused_1825_);
v___x_1813_ = v___x_1807_;
v_isShared_1814_ = v_isSharedCheck_1824_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_diag_1811_);
lean_inc(v_postponed_1810_);
lean_inc(v_zetaDeltaFVarIds_1809_);
lean_inc(v_mctx_1808_);
lean_dec(v___x_1807_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1824_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 1, v___x_1815_);
v___x_1817_ = v___x_1813_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_mctx_1808_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1823_, 2, v_zetaDeltaFVarIds_1809_);
lean_ctor_set(v_reuseFailAlloc_1823_, 3, v_postponed_1810_);
lean_ctor_set(v_reuseFailAlloc_1823_, 4, v_diag_1811_);
v___x_1817_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1818_ = lean_st_ref_set(v_a_1771_, v___x_1817_);
v___x_1819_ = lean_box(0);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1819_);
v___x_1821_ = v___x_1786_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec_ref(v_ext_1768_);
v_a_1830_ = lean_ctor_get(v___x_1783_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1783_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1783_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_1838_, lean_object* v_declName_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_1838_, v_declName_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_);
lean_dec(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec_ref(v_a_1840_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_1846_, lean_object* v_s_1847_){
_start:
{
lean_object* v_casesTypes_1848_; lean_object* v_extThms_1849_; lean_object* v_funCC_1850_; lean_object* v_ematch_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
v_casesTypes_1848_ = lean_ctor_get(v_s_1847_, 0);
v_extThms_1849_ = lean_ctor_get(v_s_1847_, 1);
v_funCC_1850_ = lean_ctor_get(v_s_1847_, 2);
v_ematch_1851_ = lean_ctor_get(v_s_1847_, 3);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_s_1847_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v_s_1847_, 4);
lean_dec(v_unused_1859_);
v___x_1853_ = v_s_1847_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_ematch_1851_);
lean_inc(v_funCC_1850_);
lean_inc(v_extThms_1849_);
lean_inc(v_casesTypes_1848_);
lean_dec(v_s_1847_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 4, v_a_1846_);
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_casesTypes_1848_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_extThms_1849_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_funCC_1850_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_ematch_1851_);
lean_ctor_set(v_reuseFailAlloc_1857_, 4, v_a_1846_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_1860_, lean_object* v_declName_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v___x_1867_; lean_object* v_ext_1868_; lean_object* v_toEnvExtension_1869_; lean_object* v_env_1870_; lean_object* v_asyncMode_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v_inj_1874_; lean_object* v___x_1875_; 
v___x_1867_ = lean_st_ref_get(v_a_1865_);
v_ext_1868_ = lean_ctor_get(v_ext_1860_, 1);
v_toEnvExtension_1869_ = lean_ctor_get(v_ext_1868_, 0);
v_env_1870_ = lean_ctor_get(v___x_1867_, 0);
lean_inc_ref(v_env_1870_);
lean_dec(v___x_1867_);
v_asyncMode_1871_ = lean_ctor_get(v_toEnvExtension_1869_, 2);
v___x_1872_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1873_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1872_, v_ext_1860_, v_env_1870_, v_asyncMode_1871_);
v_inj_1874_ = lean_ctor_get(v___x_1873_, 4);
lean_inc_ref(v_inj_1874_);
lean_dec(v___x_1873_);
v___x_1875_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_1874_, v_declName_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_);
if (lean_obj_tag(v___x_1875_) == 0)
{
lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1921_; 
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1921_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1921_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; lean_object* v_env_1881_; lean_object* v_nextMacroScope_1882_; lean_object* v_ngen_1883_; lean_object* v_auxDeclNGen_1884_; lean_object* v_traceState_1885_; lean_object* v_messages_1886_; lean_object* v_infoState_1887_; lean_object* v_snapshotTasks_1888_; lean_object* v_newDecls_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1919_; 
v___x_1880_ = lean_st_ref_take(v_a_1865_);
v_env_1881_ = lean_ctor_get(v___x_1880_, 0);
v_nextMacroScope_1882_ = lean_ctor_get(v___x_1880_, 1);
v_ngen_1883_ = lean_ctor_get(v___x_1880_, 2);
v_auxDeclNGen_1884_ = lean_ctor_get(v___x_1880_, 3);
v_traceState_1885_ = lean_ctor_get(v___x_1880_, 4);
v_messages_1886_ = lean_ctor_get(v___x_1880_, 6);
v_infoState_1887_ = lean_ctor_get(v___x_1880_, 7);
v_snapshotTasks_1888_ = lean_ctor_get(v___x_1880_, 8);
v_newDecls_1889_ = lean_ctor_get(v___x_1880_, 9);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1919_ == 0)
{
lean_object* v_unused_1920_; 
v_unused_1920_ = lean_ctor_get(v___x_1880_, 5);
lean_dec(v_unused_1920_);
v___x_1891_ = v___x_1880_;
v_isShared_1892_ = v_isSharedCheck_1919_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_newDecls_1889_);
lean_inc(v_snapshotTasks_1888_);
lean_inc(v_infoState_1887_);
lean_inc(v_messages_1886_);
lean_inc(v_traceState_1885_);
lean_inc(v_auxDeclNGen_1884_);
lean_inc(v_ngen_1883_);
lean_inc(v_nextMacroScope_1882_);
lean_inc(v_env_1881_);
lean_dec(v___x_1880_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1919_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___f_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___f_1893_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_1893_, 0, v_a_1876_);
v___x_1894_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1860_, v_env_1881_, v___f_1893_);
v___x_1895_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1892_ == 0)
{
lean_ctor_set(v___x_1891_, 5, v___x_1895_);
lean_ctor_set(v___x_1891_, 0, v___x_1894_);
v___x_1897_ = v___x_1891_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_nextMacroScope_1882_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_ngen_1883_);
lean_ctor_set(v_reuseFailAlloc_1918_, 3, v_auxDeclNGen_1884_);
lean_ctor_set(v_reuseFailAlloc_1918_, 4, v_traceState_1885_);
lean_ctor_set(v_reuseFailAlloc_1918_, 5, v___x_1895_);
lean_ctor_set(v_reuseFailAlloc_1918_, 6, v_messages_1886_);
lean_ctor_set(v_reuseFailAlloc_1918_, 7, v_infoState_1887_);
lean_ctor_set(v_reuseFailAlloc_1918_, 8, v_snapshotTasks_1888_);
lean_ctor_set(v_reuseFailAlloc_1918_, 9, v_newDecls_1889_);
v___x_1897_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v_mctx_1900_; lean_object* v_zetaDeltaFVarIds_1901_; lean_object* v_postponed_1902_; lean_object* v_diag_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1916_; 
v___x_1898_ = lean_st_ref_set(v_a_1865_, v___x_1897_);
v___x_1899_ = lean_st_ref_take(v_a_1863_);
v_mctx_1900_ = lean_ctor_get(v___x_1899_, 0);
v_zetaDeltaFVarIds_1901_ = lean_ctor_get(v___x_1899_, 2);
v_postponed_1902_ = lean_ctor_get(v___x_1899_, 3);
v_diag_1903_ = lean_ctor_get(v___x_1899_, 4);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1916_ == 0)
{
lean_object* v_unused_1917_; 
v_unused_1917_ = lean_ctor_get(v___x_1899_, 1);
lean_dec(v_unused_1917_);
v___x_1905_ = v___x_1899_;
v_isShared_1906_ = v_isSharedCheck_1916_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_diag_1903_);
lean_inc(v_postponed_1902_);
lean_inc(v_zetaDeltaFVarIds_1901_);
lean_inc(v_mctx_1900_);
lean_dec(v___x_1899_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1916_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1907_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1906_ == 0)
{
lean_ctor_set(v___x_1905_, 1, v___x_1907_);
v___x_1909_ = v___x_1905_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_mctx_1900_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1915_, 2, v_zetaDeltaFVarIds_1901_);
lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_postponed_1902_);
lean_ctor_set(v_reuseFailAlloc_1915_, 4, v_diag_1903_);
v___x_1909_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1913_; 
v___x_1910_ = lean_st_ref_set(v_a_1863_, v___x_1909_);
v___x_1911_ = lean_box(0);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1911_);
v___x_1913_ = v___x_1878_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v___x_1911_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec_ref(v_ext_1860_);
v_a_1922_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1875_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1875_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___boxed(lean_object* v_ext_1930_, lean_object* v_declName_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_a_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_1930_, v_declName_1931_, v_a_1932_, v_a_1933_, v_a_1934_, v_a_1935_);
lean_dec(v_a_1935_);
lean_dec_ref(v_a_1934_);
lean_dec(v_a_1933_);
lean_dec_ref(v_a_1932_);
return v_res_1937_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_1938_, lean_object* v_i_1939_, lean_object* v_k_1940_){
_start:
{
lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = lean_array_get_size(v_keys_1938_);
v___x_1942_ = lean_nat_dec_lt(v_i_1939_, v___x_1941_);
if (v___x_1942_ == 0)
{
lean_dec(v_i_1939_);
return v___x_1942_;
}
else
{
lean_object* v_k_x27_1943_; uint8_t v___x_1944_; 
v_k_x27_1943_ = lean_array_fget_borrowed(v_keys_1938_, v_i_1939_);
v___x_1944_ = lean_name_eq(v_k_1940_, v_k_x27_1943_);
if (v___x_1944_ == 0)
{
lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1945_ = lean_unsigned_to_nat(1u);
v___x_1946_ = lean_nat_add(v_i_1939_, v___x_1945_);
lean_dec(v_i_1939_);
v_i_1939_ = v___x_1946_;
goto _start;
}
else
{
lean_dec(v_i_1939_);
return v___x_1944_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_1948_, lean_object* v_i_1949_, lean_object* v_k_1950_){
_start:
{
uint8_t v_res_1951_; lean_object* v_r_1952_; 
v_res_1951_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_1948_, v_i_1949_, v_k_1950_);
lean_dec(v_k_1950_);
lean_dec_ref(v_keys_1948_);
v_r_1952_ = lean_box(v_res_1951_);
return v_r_1952_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_1953_; size_t v___x_1954_; size_t v___x_1955_; 
v___x_1953_ = ((size_t)5ULL);
v___x_1954_ = ((size_t)1ULL);
v___x_1955_ = lean_usize_shift_left(v___x_1954_, v___x_1953_);
return v___x_1955_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_1956_; size_t v___x_1957_; size_t v___x_1958_; 
v___x_1956_ = ((size_t)1ULL);
v___x_1957_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__0);
v___x_1958_ = lean_usize_sub(v___x_1957_, v___x_1956_);
return v___x_1958_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_1959_, size_t v_x_1960_, lean_object* v_x_1961_){
_start:
{
if (lean_obj_tag(v_x_1959_) == 0)
{
lean_object* v_es_1962_; lean_object* v___x_1963_; size_t v___x_1964_; size_t v___x_1965_; size_t v___x_1966_; lean_object* v_j_1967_; lean_object* v___x_1968_; 
v_es_1962_ = lean_ctor_get(v_x_1959_, 0);
v___x_1963_ = lean_box(2);
v___x_1964_ = ((size_t)5ULL);
v___x_1965_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1);
v___x_1966_ = lean_usize_land(v_x_1960_, v___x_1965_);
v_j_1967_ = lean_usize_to_nat(v___x_1966_);
v___x_1968_ = lean_array_get_borrowed(v___x_1963_, v_es_1962_, v_j_1967_);
lean_dec(v_j_1967_);
switch(lean_obj_tag(v___x_1968_))
{
case 0:
{
lean_object* v_key_1969_; uint8_t v___x_1970_; 
v_key_1969_ = lean_ctor_get(v___x_1968_, 0);
v___x_1970_ = lean_name_eq(v_x_1961_, v_key_1969_);
return v___x_1970_;
}
case 1:
{
lean_object* v_node_1971_; size_t v___x_1972_; 
v_node_1971_ = lean_ctor_get(v___x_1968_, 0);
v___x_1972_ = lean_usize_shift_right(v_x_1960_, v___x_1964_);
v_x_1959_ = v_node_1971_;
v_x_1960_ = v___x_1972_;
goto _start;
}
default: 
{
uint8_t v___x_1974_; 
v___x_1974_ = 0;
return v___x_1974_;
}
}
}
else
{
lean_object* v_ks_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v_ks_1975_ = lean_ctor_get(v_x_1959_, 0);
v___x_1976_ = lean_unsigned_to_nat(0u);
v___x_1977_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_1975_, v___x_1976_, v_x_1961_);
return v___x_1977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_1978_, lean_object* v_x_1979_, lean_object* v_x_1980_){
_start:
{
size_t v_x_344__boxed_1981_; uint8_t v_res_1982_; lean_object* v_r_1983_; 
v_x_344__boxed_1981_ = lean_unbox_usize(v_x_1979_);
lean_dec(v_x_1979_);
v_res_1982_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_1978_, v_x_344__boxed_1981_, v_x_1980_);
lean_dec(v_x_1980_);
lean_dec_ref(v_x_1978_);
v_r_1983_ = lean_box(v_res_1982_);
return v_r_1983_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1984_; uint64_t v___x_1985_; 
v___x_1984_ = lean_unsigned_to_nat(1723u);
v___x_1985_ = lean_uint64_of_nat(v___x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_1986_, lean_object* v_x_1987_){
_start:
{
uint64_t v___y_1989_; 
if (lean_obj_tag(v_x_1987_) == 0)
{
uint64_t v___x_1992_; 
v___x_1992_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_1989_ = v___x_1992_;
goto v___jp_1988_;
}
else
{
uint64_t v_hash_1993_; 
v_hash_1993_ = lean_ctor_get_uint64(v_x_1987_, sizeof(void*)*2);
v___y_1989_ = v_hash_1993_;
goto v___jp_1988_;
}
v___jp_1988_:
{
size_t v___x_1990_; uint8_t v___x_1991_; 
v___x_1990_ = lean_uint64_to_usize(v___y_1989_);
v___x_1991_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_1986_, v___x_1990_, v_x_1987_);
return v___x_1991_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_1994_, lean_object* v_x_1995_){
_start:
{
uint8_t v_res_1996_; lean_object* v_r_1997_; 
v_res_1996_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_1994_, v_x_1995_);
lean_dec(v_x_1995_);
lean_dec_ref(v_x_1994_);
v_r_1997_ = lean_box(v_res_1996_);
return v_r_1997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_1998_, lean_object* v_declName_1999_, lean_object* v_a_2000_){
_start:
{
lean_object* v___x_2002_; lean_object* v_ext_2003_; lean_object* v_toEnvExtension_2004_; lean_object* v_env_2005_; lean_object* v_asyncMode_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v_extThms_2009_; uint8_t v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2002_ = lean_st_ref_get(v_a_2000_);
v_ext_2003_ = lean_ctor_get(v_ext_1998_, 1);
v_toEnvExtension_2004_ = lean_ctor_get(v_ext_2003_, 0);
v_env_2005_ = lean_ctor_get(v___x_2002_, 0);
lean_inc_ref(v_env_2005_);
lean_dec(v___x_2002_);
v_asyncMode_2006_ = lean_ctor_get(v_toEnvExtension_2004_, 2);
v___x_2007_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2008_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2007_, v_ext_1998_, v_env_2005_, v_asyncMode_2006_);
v_extThms_2009_ = lean_ctor_get(v___x_2008_, 1);
lean_inc_ref(v_extThms_2009_);
lean_dec(v___x_2008_);
v___x_2010_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_2009_, v_declName_1999_);
lean_dec_ref(v_extThms_2009_);
v___x_2011_ = lean_box(v___x_2010_);
v___x_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2011_);
return v___x_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_2013_, lean_object* v_declName_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2013_, v_declName_2014_, v_a_2015_);
lean_dec(v_a_2015_);
lean_dec(v_declName_2014_);
lean_dec_ref(v_ext_2013_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_2018_, lean_object* v_declName_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2018_, v_declName_2019_, v_a_2021_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_2024_, lean_object* v_declName_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_2024_, v_declName_2025_, v_a_2026_, v_a_2027_);
lean_dec(v_a_2027_);
lean_dec_ref(v_a_2026_);
lean_dec(v_declName_2025_);
lean_dec_ref(v_ext_2024_);
return v_res_2029_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_2030_, lean_object* v_x_2031_, lean_object* v_x_2032_){
_start:
{
uint8_t v___x_2033_; 
v___x_2033_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2031_, v_x_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_2034_, lean_object* v_x_2035_, lean_object* v_x_2036_){
_start:
{
uint8_t v_res_2037_; lean_object* v_r_2038_; 
v_res_2037_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_2034_, v_x_2035_, v_x_2036_);
lean_dec(v_x_2036_);
lean_dec_ref(v_x_2035_);
v_r_2038_ = lean_box(v_res_2037_);
return v_r_2038_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_2039_, lean_object* v_x_2040_, size_t v_x_2041_, lean_object* v_x_2042_){
_start:
{
uint8_t v___x_2043_; 
v___x_2043_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2040_, v_x_2041_, v_x_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2044_, lean_object* v_x_2045_, lean_object* v_x_2046_, lean_object* v_x_2047_){
_start:
{
size_t v_x_441__boxed_2048_; uint8_t v_res_2049_; lean_object* v_r_2050_; 
v_x_441__boxed_2048_ = lean_unbox_usize(v_x_2046_);
lean_dec(v_x_2046_);
v_res_2049_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_2044_, v_x_2045_, v_x_441__boxed_2048_, v_x_2047_);
lean_dec(v_x_2047_);
lean_dec_ref(v_x_2045_);
v_r_2050_ = lean_box(v_res_2049_);
return v_r_2050_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2051_, lean_object* v_keys_2052_, lean_object* v_vals_2053_, lean_object* v_heq_2054_, lean_object* v_i_2055_, lean_object* v_k_2056_){
_start:
{
uint8_t v___x_2057_; 
v___x_2057_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_2052_, v_i_2055_, v_k_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2058_, lean_object* v_keys_2059_, lean_object* v_vals_2060_, lean_object* v_heq_2061_, lean_object* v_i_2062_, lean_object* v_k_2063_){
_start:
{
uint8_t v_res_2064_; lean_object* v_r_2065_; 
v_res_2064_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_2058_, v_keys_2059_, v_vals_2060_, v_heq_2061_, v_i_2062_, v_k_2063_);
lean_dec(v_k_2063_);
lean_dec_ref(v_vals_2060_);
lean_dec_ref(v_keys_2059_);
v_r_2065_ = lean_box(v_res_2064_);
return v_r_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_2066_, lean_object* v_declName_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v___x_2070_; lean_object* v_ext_2071_; lean_object* v_toEnvExtension_2072_; lean_object* v_env_2073_; lean_object* v_asyncMode_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v_inj_2077_; lean_object* v___x_2078_; uint8_t v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2070_ = lean_st_ref_get(v_a_2068_);
v_ext_2071_ = lean_ctor_get(v_ext_2066_, 1);
v_toEnvExtension_2072_ = lean_ctor_get(v_ext_2071_, 0);
v_env_2073_ = lean_ctor_get(v___x_2070_, 0);
lean_inc_ref(v_env_2073_);
lean_dec(v___x_2070_);
v_asyncMode_2074_ = lean_ctor_get(v_toEnvExtension_2072_, 2);
v___x_2075_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2076_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2075_, v_ext_2066_, v_env_2073_, v_asyncMode_2074_);
v_inj_2077_ = lean_ctor_get(v___x_2076_, 4);
lean_inc_ref(v_inj_2077_);
lean_dec(v___x_2076_);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v_declName_2067_);
v___x_2079_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_2077_, v___x_2078_);
lean_dec_ref(v___x_2078_);
lean_dec_ref(v_inj_2077_);
v___x_2080_ = lean_box(v___x_2079_);
v___x_2081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_2082_, lean_object* v_declName_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2082_, v_declName_2083_, v_a_2084_);
lean_dec(v_a_2084_);
lean_dec_ref(v_ext_2082_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_2087_, lean_object* v_declName_2088_, lean_object* v_a_2089_, lean_object* v_a_2090_){
_start:
{
lean_object* v___x_2092_; 
v___x_2092_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2087_, v_declName_2088_, v_a_2090_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_2093_, lean_object* v_declName_2094_, lean_object* v_a_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_2093_, v_declName_2094_, v_a_2095_, v_a_2096_);
lean_dec(v_a_2096_);
lean_dec_ref(v_a_2095_);
lean_dec_ref(v_ext_2093_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_2099_, lean_object* v_declName_2100_, lean_object* v_a_2101_){
_start:
{
lean_object* v___x_2103_; lean_object* v_ext_2104_; lean_object* v_toEnvExtension_2105_; lean_object* v_env_2106_; lean_object* v_asyncMode_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v_funCC_2110_; uint8_t v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2103_ = lean_st_ref_get(v_a_2101_);
v_ext_2104_ = lean_ctor_get(v_ext_2099_, 1);
v_toEnvExtension_2105_ = lean_ctor_get(v_ext_2104_, 0);
v_env_2106_ = lean_ctor_get(v___x_2103_, 0);
lean_inc_ref(v_env_2106_);
lean_dec(v___x_2103_);
v_asyncMode_2107_ = lean_ctor_get(v_toEnvExtension_2105_, 2);
v___x_2108_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2109_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2108_, v_ext_2099_, v_env_2106_, v_asyncMode_2107_);
v_funCC_2110_ = lean_ctor_get(v___x_2109_, 2);
lean_inc(v_funCC_2110_);
lean_dec(v___x_2109_);
v___x_2111_ = l_Lean_NameSet_contains(v_funCC_2110_, v_declName_2100_);
lean_dec(v_funCC_2110_);
v___x_2112_ = lean_box(v___x_2111_);
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_2114_, lean_object* v_declName_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2114_, v_declName_2115_, v_a_2116_);
lean_dec(v_a_2116_);
lean_dec(v_declName_2115_);
lean_dec_ref(v_ext_2114_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_2119_, lean_object* v_declName_2120_, lean_object* v_a_2121_, lean_object* v_a_2122_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2119_, v_declName_2120_, v_a_2122_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_2125_, lean_object* v_declName_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_2125_, v_declName_2126_, v_a_2127_, v_a_2128_);
lean_dec(v_a_2128_);
lean_dec_ref(v_a_2127_);
lean_dec(v_declName_2126_);
lean_dec_ref(v_ext_2125_);
return v_res_2130_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2154_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_2155_ = l_Lean_mkAtom(v___x_2154_);
return v___x_2155_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_2157_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2158_ = lean_array_push(v___x_2157_, v___x_2156_);
return v___x_2158_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_2168_ = l_Lean_mkAtom(v___x_2167_);
return v___x_2168_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2169_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_2170_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2171_ = lean_array_push(v___x_2170_, v___x_2169_);
return v___x_2171_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2172_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_2173_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_2174_ = lean_box(2);
v___x_2175_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
lean_ctor_set(v___x_2175_, 1, v___x_2173_);
lean_ctor_set(v___x_2175_, 2, v___x_2172_);
return v___x_2175_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_2177_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_2178_ = lean_array_push(v___x_2177_, v___x_2176_);
return v___x_2178_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2179_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_2180_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_2181_ = lean_box(2);
v___x_2182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v___x_2180_);
lean_ctor_set(v___x_2182_, 2, v___x_2179_);
return v___x_2182_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_2184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2185_ = lean_array_push(v___x_2184_, v___x_2183_);
return v___x_2185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2186_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_2187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_2188_ = lean_box(2);
v___x_2189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
lean_ctor_set(v___x_2189_, 1, v___x_2187_);
lean_ctor_set(v___x_2189_, 2, v___x_2186_);
return v___x_2189_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_2191_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2192_ = lean_array_push(v___x_2191_, v___x_2190_);
return v___x_2192_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2193_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_2194_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_2195_ = lean_box(2);
v___x_2196_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2195_);
lean_ctor_set(v___x_2196_, 1, v___x_2194_);
lean_ctor_set(v___x_2196_, 2, v___x_2193_);
return v___x_2196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_2198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2199_ = lean_array_push(v___x_2198_, v___x_2197_);
return v___x_2199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2200_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_2201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_2202_ = lean_box(2);
v___x_2203_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
lean_ctor_set(v___x_2203_, 1, v___x_2201_);
lean_ctor_set(v___x_2203_, 2, v___x_2200_);
return v___x_2203_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_2205_, lean_object* v_ext_2206_, lean_object* v_____r_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
uint8_t v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = 0;
lean_inc(v_declName_2205_);
v___x_2214_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_2205_, v___x_2213_, v___y_2210_, v___y_2211_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; uint8_t v___x_2216_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref(v___x_2214_);
v___x_2216_ = lean_unbox(v_a_2215_);
lean_dec(v_a_2215_);
if (v___x_2216_ == 0)
{
lean_object* v___x_2217_; lean_object* v_a_2218_; uint8_t v___x_2219_; 
v___x_2217_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2206_, v_declName_2205_, v___y_2211_);
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref(v___x_2217_);
v___x_2219_ = lean_unbox(v_a_2218_);
lean_dec(v_a_2218_);
if (v___x_2219_ == 0)
{
lean_object* v___x_2220_; lean_object* v_a_2221_; uint8_t v___x_2222_; 
lean_inc(v_declName_2205_);
v___x_2220_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2206_, v_declName_2205_, v___y_2211_);
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref(v___x_2220_);
v___x_2222_ = lean_unbox(v_a_2221_);
lean_dec(v_a_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v_a_2224_; uint8_t v___x_2225_; 
v___x_2223_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2206_, v_declName_2205_, v___y_2211_);
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref(v___x_2223_);
v___x_2225_ = lean_unbox(v_a_2224_);
lean_dec(v_a_2224_);
if (v___x_2225_ == 0)
{
lean_object* v___x_2226_; 
v___x_2226_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_2206_, v_declName_2205_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
return v___x_2226_;
}
else
{
lean_object* v___x_2227_; 
v___x_2227_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2206_, v_declName_2205_, v___y_2210_, v___y_2211_);
return v___x_2227_;
}
}
else
{
lean_object* v___x_2228_; 
v___x_2228_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_2206_, v_declName_2205_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_);
return v___x_2228_;
}
}
else
{
lean_object* v___x_2229_; 
v___x_2229_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2206_, v_declName_2205_, v___y_2210_, v___y_2211_);
return v___x_2229_;
}
}
else
{
lean_object* v___x_2230_; 
v___x_2230_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2206_, v_declName_2205_, v___y_2210_, v___y_2211_);
return v___x_2230_;
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec_ref(v_ext_2206_);
lean_dec(v_declName_2205_);
v_a_2231_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2214_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2214_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_2239_, lean_object* v_ext_2240_, lean_object* v_____r_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2239_, v_ext_2240_, v_____r_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object* v_msgData_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v___x_2254_; lean_object* v_env_2255_; lean_object* v___x_2256_; lean_object* v_mctx_2257_; lean_object* v_lctx_2258_; lean_object* v_options_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2254_ = lean_st_ref_get(v___y_2252_);
v_env_2255_ = lean_ctor_get(v___x_2254_, 0);
lean_inc_ref(v_env_2255_);
lean_dec(v___x_2254_);
v___x_2256_ = lean_st_ref_get(v___y_2250_);
v_mctx_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc_ref(v_mctx_2257_);
lean_dec(v___x_2256_);
v_lctx_2258_ = lean_ctor_get(v___y_2249_, 2);
v_options_2259_ = lean_ctor_get(v___y_2251_, 2);
lean_inc_ref(v_options_2259_);
lean_inc_ref(v_lctx_2258_);
v___x_2260_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2260_, 0, v_env_2255_);
lean_ctor_set(v___x_2260_, 1, v_mctx_2257_);
lean_ctor_set(v___x_2260_, 2, v_lctx_2258_);
lean_ctor_set(v___x_2260_, 3, v_options_2259_);
v___x_2261_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
lean_ctor_set(v___x_2261_, 1, v_msgData_2248_);
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object* v_msgData_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msgData_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
return v_res_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_ref_2276_; lean_object* v___x_2277_; lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2286_; 
v_ref_2276_ = lean_ctor_get(v___y_2273_, 5);
v___x_2277_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2270_, v___y_2271_, v___y_2272_, v___y_2273_, v___y_2274_);
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2286_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2286_ == 0)
{
v___x_2280_ = v___x_2277_;
v_isShared_2281_ = v_isSharedCheck_2286_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2286_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; lean_object* v___x_2284_; 
lean_inc(v_ref_2276_);
v___x_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2282_, 0, v_ref_2276_);
lean_ctor_set(v___x_2282_, 1, v_a_2278_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set_tag(v___x_2280_, 1);
lean_ctor_set(v___x_2280_, 0, v___x_2282_);
v___x_2284_ = v___x_2280_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v___x_2282_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
return v_res_2293_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2300_; uint64_t v___x_2301_; 
v___x_2300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2301_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2300_);
return v___x_2301_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_2303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2304_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
lean_ctor_set_uint64(v___x_2304_, sizeof(void*)*1, v___x_2302_);
return v___x_2304_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2305_; 
v___x_2305_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2305_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
return v___x_2307_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2308_ = lean_box(1);
v___x_2309_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2310_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
lean_ctor_set(v___x_2311_, 1, v___x_2309_);
lean_ctor_set(v___x_2311_, 2, v___x_2308_);
return v___x_2311_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2314_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2315_ = lean_unsigned_to_nat(0u);
v___x_2316_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
lean_ctor_set(v___x_2316_, 2, v___x_2315_);
lean_ctor_set(v___x_2316_, 3, v___x_2315_);
lean_ctor_set(v___x_2316_, 4, v___x_2314_);
lean_ctor_set(v___x_2316_, 5, v___x_2314_);
lean_ctor_set(v___x_2316_, 6, v___x_2314_);
lean_ctor_set(v___x_2316_, 7, v___x_2314_);
lean_ctor_set(v___x_2316_, 8, v___x_2314_);
lean_ctor_set(v___x_2316_, 9, v___x_2314_);
return v___x_2316_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2318_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
lean_ctor_set(v___x_2318_, 2, v___x_2317_);
lean_ctor_set(v___x_2318_, 3, v___x_2317_);
lean_ctor_set(v___x_2318_, 4, v___x_2317_);
lean_ctor_set(v___x_2318_, 5, v___x_2317_);
return v___x_2318_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
lean_ctor_set(v___x_2320_, 2, v___x_2319_);
lean_ctor_set(v___x_2320_, 3, v___x_2319_);
lean_ctor_set(v___x_2320_, 4, v___x_2319_);
return v___x_2320_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10));
v___x_2323_ = l_Lean_stringToMessageData(v___x_2322_);
return v___x_2323_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12));
v___x_2326_ = l_Lean_stringToMessageData(v___x_2325_);
return v___x_2326_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14));
v___x_2329_ = l_Lean_stringToMessageData(v___x_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v___x_2330_, lean_object* v_ext_2331_, uint8_t v_showInfo_2332_, lean_object* v_attrName_2333_, lean_object* v_declName_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
uint8_t v___x_2338_; uint8_t v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___y_2353_; 
v___x_2338_ = 1;
v___x_2339_ = 0;
v___x_2340_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_2341_ = lean_unsigned_to_nat(0u);
v___x_2342_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2343_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_2344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6));
v___x_2345_ = lean_box(0);
lean_inc(v___x_2330_);
v___x_2346_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2346_, 0, v___x_2340_);
lean_ctor_set(v___x_2346_, 1, v___x_2330_);
lean_ctor_set(v___x_2346_, 2, v___x_2343_);
lean_ctor_set(v___x_2346_, 3, v___x_2344_);
lean_ctor_set(v___x_2346_, 4, v___x_2345_);
lean_ctor_set(v___x_2346_, 5, v___x_2341_);
lean_ctor_set(v___x_2346_, 6, v___x_2345_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*7, v___x_2339_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*7 + 1, v___x_2339_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*7 + 2, v___x_2339_);
lean_ctor_set_uint8(v___x_2346_, sizeof(void*)*7 + 3, v___x_2338_);
v___x_2347_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_2348_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_2349_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_2350_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2347_);
lean_ctor_set(v___x_2350_, 1, v___x_2348_);
lean_ctor_set(v___x_2350_, 2, v___x_2330_);
lean_ctor_set(v___x_2350_, 3, v___x_2342_);
lean_ctor_set(v___x_2350_, 4, v___x_2349_);
v___x_2351_ = lean_st_mk_ref(v___x_2350_);
if (v_showInfo_2332_ == 0)
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
lean_dec(v_attrName_2333_);
v___x_2363_ = lean_box(0);
v___x_2364_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2334_, v_ext_2331_, v___x_2363_, v___x_2346_, v___x_2351_, v___y_2335_, v___y_2336_);
lean_dec_ref(v___x_2346_);
v___y_2353_ = v___x_2364_;
goto v___jp_2352_;
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
lean_dec(v_declName_2334_);
lean_dec_ref(v_ext_2331_);
v___x_2365_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11);
v___x_2366_ = l_Lean_MessageData_ofName(v_attrName_2333_);
lean_inc_ref(v___x_2366_);
v___x_2367_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2365_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13);
v___x_2369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2369_, 0, v___x_2367_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
v___x_2370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
lean_ctor_set(v___x_2370_, 1, v___x_2366_);
v___x_2371_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15);
v___x_2372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2370_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2372_, v___x_2346_, v___x_2351_, v___y_2335_, v___y_2336_);
lean_dec_ref(v___x_2346_);
v___y_2353_ = v___x_2373_;
goto v___jp_2352_;
}
v___jp_2352_:
{
if (lean_obj_tag(v___y_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2362_; 
v_a_2354_ = lean_ctor_get(v___y_2353_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___y_2353_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2356_ = v___y_2353_;
v_isShared_2357_ = v_isSharedCheck_2362_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___y_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2362_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2358_; lean_object* v___x_2360_; 
v___x_2358_ = lean_st_ref_get(v___x_2351_);
lean_dec(v___x_2351_);
lean_dec(v___x_2358_);
if (v_isShared_2357_ == 0)
{
v___x_2360_ = v___x_2356_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2354_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
else
{
lean_dec(v___x_2351_);
return v___y_2353_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v___x_2374_, lean_object* v_ext_2375_, lean_object* v_showInfo_2376_, lean_object* v_attrName_2377_, lean_object* v_declName_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
uint8_t v_showInfo_boxed_2382_; lean_object* v_res_2383_; 
v_showInfo_boxed_2382_ = lean_unbox(v_showInfo_2376_);
v_res_2383_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v___x_2374_, v_ext_2375_, v_showInfo_boxed_2382_, v_attrName_2377_, v_declName_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_2386_, uint8_t v_attrKind_2387_, uint8_t v_showInfo_2388_, uint8_t v_minIndexable_2389_, lean_object* v_as_x27_2390_, lean_object* v_b_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_){
_start:
{
if (lean_obj_tag(v_as_x27_2390_) == 0)
{
lean_object* v___x_2397_; 
lean_dec_ref(v_ext_2386_);
v___x_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2397_, 0, v_b_2391_);
return v___x_2397_;
}
else
{
lean_object* v_head_2398_; lean_object* v_tail_2399_; lean_object* v___x_2400_; 
v_head_2398_ = lean_ctor_get(v_as_x27_2390_, 0);
v_tail_2399_ = lean_ctor_get(v_as_x27_2390_, 1);
v___x_2400_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2395_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref(v___x_2400_);
v___x_2402_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v_head_2398_);
lean_inc_ref(v_ext_2386_);
v___x_2403_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2386_, v_head_2398_, v_attrKind_2387_, v___x_2402_, v_a_2401_, v_showInfo_2388_, v_minIndexable_2389_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v___x_2404_; 
lean_dec_ref(v___x_2403_);
v___x_2404_ = lean_box(0);
v_as_x27_2390_ = v_tail_2399_;
v_b_2391_ = v___x_2404_;
goto _start;
}
else
{
lean_dec_ref(v_ext_2386_);
return v___x_2403_;
}
}
else
{
lean_object* v_a_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
lean_dec_ref(v_ext_2386_);
v_a_2406_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2400_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_a_2406_);
lean_dec(v___x_2400_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_a_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_2414_, lean_object* v_attrKind_2415_, lean_object* v_showInfo_2416_, lean_object* v_minIndexable_2417_, lean_object* v_as_x27_2418_, lean_object* v_b_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
uint8_t v_attrKind_boxed_2425_; uint8_t v_showInfo_boxed_2426_; uint8_t v_minIndexable_boxed_2427_; lean_object* v_res_2428_; 
v_attrKind_boxed_2425_ = lean_unbox(v_attrKind_2415_);
v_showInfo_boxed_2426_ = lean_unbox(v_showInfo_2416_);
v_minIndexable_boxed_2427_ = lean_unbox(v_minIndexable_2417_);
v_res_2428_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2414_, v_attrKind_boxed_2425_, v_showInfo_boxed_2426_, v_minIndexable_boxed_2427_, v_as_x27_2418_, v_b_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v_as_x27_2418_);
return v_res_2428_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_2431_ = l_Lean_stringToMessageData(v___x_2430_);
return v___x_2431_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_2434_ = l_Lean_stringToMessageData(v___x_2433_);
return v___x_2434_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_2437_ = l_Lean_stringToMessageData(v___x_2436_);
return v___x_2437_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_2440_ = l_Lean_stringToMessageData(v___x_2439_);
return v___x_2440_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10));
v___x_2446_ = l_Lean_stringToMessageData(v___x_2445_);
return v___x_2446_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13(void){
_start:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12));
v___x_2449_ = l_Lean_stringToMessageData(v___x_2448_);
return v___x_2449_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15(void){
_start:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2451_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14));
v___x_2452_ = l_Lean_stringToMessageData(v___x_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_stx_2453_, lean_object* v_ext_2454_, lean_object* v_declName_2455_, uint8_t v_attrKind_2456_, uint8_t v_showInfo_2457_, uint8_t v_minIndexable_2458_, uint8_t v___x_2459_, lean_object* v_attrName_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___y_2467_; lean_object* v___y_2468_; lean_object* v___y_2469_; lean_object* v___y_2470_; lean_object* v___x_2494_; 
v___x_2494_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_2453_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref(v___x_2494_);
switch(lean_obj_tag(v_a_2495_))
{
case 0:
{
lean_object* v_k_2496_; 
lean_dec(v_attrName_2460_);
lean_dec(v_stx_2453_);
v_k_2496_ = lean_ctor_get(v_a_2495_, 0);
lean_inc(v_k_2496_);
lean_dec_ref(v_a_2495_);
if (lean_obj_tag(v_k_2496_) == 9)
{
lean_object* v___x_2497_; 
lean_dec(v_declName_2455_);
lean_dec_ref(v_ext_2454_);
v___x_2497_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_2463_, v___y_2464_);
return v___x_2497_;
}
else
{
lean_object* v___x_2498_; 
v___x_2498_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2464_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; lean_object* v___x_2500_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref(v___x_2498_);
v___x_2500_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2454_, v_declName_2455_, v_attrKind_2456_, v_k_2496_, v_a_2499_, v_showInfo_2457_, v_minIndexable_2458_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2500_;
}
else
{
lean_object* v_a_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2508_; 
lean_dec(v_k_2496_);
lean_dec(v_declName_2455_);
lean_dec_ref(v_ext_2454_);
v_a_2501_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2508_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2503_ = v___x_2498_;
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_a_2501_);
lean_dec(v___x_2498_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2508_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2506_; 
if (v_isShared_2504_ == 0)
{
v___x_2506_ = v___x_2503_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
}
}
case 1:
{
uint8_t v_eager_2509_; lean_object* v___x_2510_; 
lean_dec(v_attrName_2460_);
lean_dec(v_stx_2453_);
v_eager_2509_ = lean_ctor_get_uint8(v_a_2495_, 0);
lean_dec_ref(v_a_2495_);
v___x_2510_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2454_, v_declName_2455_, v_eager_2509_, v_attrKind_2456_, v___y_2463_, v___y_2464_);
return v___x_2510_;
}
case 2:
{
lean_object* v___x_2511_; 
lean_dec(v_stx_2453_);
lean_inc(v_declName_2455_);
v___x_2511_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_2455_, v___x_2459_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref(v___x_2511_);
if (lean_obj_tag(v_a_2512_) == 1)
{
lean_object* v_val_2513_; lean_object* v_ctors_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
lean_dec(v_attrName_2460_);
lean_dec(v_declName_2455_);
v_val_2513_ = lean_ctor_get(v_a_2512_, 0);
lean_inc(v_val_2513_);
lean_dec_ref(v_a_2512_);
v_ctors_2514_ = lean_ctor_get(v_val_2513_, 4);
lean_inc(v_ctors_2514_);
lean_dec(v_val_2513_);
v___x_2515_ = lean_box(0);
v___x_2516_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2454_, v_attrKind_2456_, v_showInfo_2457_, v_minIndexable_2458_, v_ctors_2514_, v___x_2515_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v_ctors_2514_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; 
v_unused_2524_ = lean_ctor_get(v___x_2516_, 0);
lean_dec(v_unused_2524_);
v___x_2518_ = v___x_2516_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_dec(v___x_2516_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2515_);
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2515_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
else
{
return v___x_2516_;
}
}
else
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
lean_dec(v_a_2512_);
lean_dec_ref(v_ext_2454_);
v___x_2525_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3);
v___x_2526_ = l_Lean_MessageData_ofName(v_attrName_2460_);
v___x_2527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2525_);
lean_ctor_set(v___x_2527_, 1, v___x_2526_);
v___x_2528_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_2529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2527_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
v___x_2530_ = l_Lean_MessageData_ofConstName(v_declName_2455_, v___x_2459_);
v___x_2531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2529_);
lean_ctor_set(v___x_2531_, 1, v___x_2530_);
v___x_2532_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_2533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2531_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2533_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2534_;
}
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_attrName_2460_);
lean_dec(v_declName_2455_);
lean_dec_ref(v_ext_2454_);
v_a_2535_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2511_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2511_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
case 3:
{
lean_object* v___x_2543_; 
lean_dec(v_attrName_2460_);
lean_inc(v_declName_2455_);
v___x_2543_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_2455_, v___x_2459_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref(v___x_2543_);
if (lean_obj_tag(v_a_2544_) == 1)
{
lean_object* v_val_2545_; lean_object* v___x_2546_; 
lean_dec(v_declName_2455_);
lean_dec(v_stx_2453_);
v_val_2545_ = lean_ctor_get(v_a_2544_, 0);
lean_inc_n(v_val_2545_, 2);
lean_dec_ref(v_a_2544_);
lean_inc_ref(v_ext_2454_);
v___x_2546_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2454_, v_val_2545_, v___x_2459_, v_attrKind_2456_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v___x_2547_; 
lean_dec_ref(v___x_2546_);
v___x_2547_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_2545_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2568_; 
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2568_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2568_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
if (lean_obj_tag(v_a_2548_) == 1)
{
lean_object* v_val_2552_; lean_object* v_ctors_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
lean_del_object(v___x_2550_);
v_val_2552_ = lean_ctor_get(v_a_2548_, 0);
lean_inc(v_val_2552_);
lean_dec_ref(v_a_2548_);
v_ctors_2553_ = lean_ctor_get(v_val_2552_, 4);
lean_inc(v_ctors_2553_);
lean_dec(v_val_2552_);
v___x_2554_ = lean_box(0);
v___x_2555_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2454_, v_attrKind_2456_, v_showInfo_2457_, v_minIndexable_2458_, v_ctors_2553_, v___x_2554_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v_ctors_2553_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v___x_2555_, 0);
lean_dec(v_unused_2563_);
v___x_2557_ = v___x_2555_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_dec(v___x_2555_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v___x_2554_);
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2554_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
else
{
return v___x_2555_;
}
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2566_; 
lean_dec(v_a_2548_);
lean_dec_ref(v_ext_2454_);
v___x_2564_ = lean_box(0);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 0, v___x_2564_);
v___x_2566_ = v___x_2550_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec_ref(v_ext_2454_);
v_a_2569_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2547_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2547_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
lean_dec(v_val_2545_);
lean_dec_ref(v_ext_2454_);
return v___x_2546_;
}
}
else
{
lean_object* v___x_2577_; 
lean_dec(v_a_2544_);
v___x_2577_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2464_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2579_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref(v___x_2577_);
v___x_2579_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_2454_, v_stx_2453_, v_declName_2455_, v_attrKind_2456_, v_a_2578_, v_minIndexable_2458_, v_showInfo_2457_, v___x_2459_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2579_;
}
else
{
lean_object* v_a_2580_; lean_object* v___x_2582_; uint8_t v_isShared_2583_; uint8_t v_isSharedCheck_2587_; 
lean_dec(v_declName_2455_);
lean_dec_ref(v_ext_2454_);
lean_dec(v_stx_2453_);
v_a_2580_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2582_ = v___x_2577_;
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
else
{
lean_inc(v_a_2580_);
lean_dec(v___x_2577_);
v___x_2582_ = lean_box(0);
v_isShared_2583_ = v_isSharedCheck_2587_;
goto v_resetjp_2581_;
}
v_resetjp_2581_:
{
lean_object* v___x_2585_; 
if (v_isShared_2583_ == 0)
{
v___x_2585_ = v___x_2582_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2580_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec(v_declName_2455_);
lean_dec_ref(v_ext_2454_);
lean_dec(v_stx_2453_);
v_a_2588_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2543_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2543_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
case 4:
{
lean_object* v___x_2596_; 
lean_dec(v_attrName_2460_);
lean_dec(v_stx_2453_);
v___x_2596_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2454_, v_declName_2455_, v_attrKind_2456_, v___y_2463_, v___y_2464_);
return v___x_2596_;
}
case 5:
{
lean_object* v_prio_2597_; lean_object* v___x_2598_; uint8_t v___x_2599_; 
lean_dec_ref(v_ext_2454_);
lean_dec(v_stx_2453_);
v_prio_2597_ = lean_ctor_get(v_a_2495_, 0);
lean_inc(v_prio_2597_);
lean_dec_ref(v_a_2495_);
v___x_2598_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2599_ = lean_name_eq(v_attrName_2460_, v___x_2598_);
lean_dec(v_attrName_2460_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec(v_prio_2597_);
lean_dec(v_declName_2455_);
v___x_2600_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11);
v___x_2601_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2600_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2601_;
}
else
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_2455_, v_attrKind_2456_, v_prio_2597_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2602_;
}
}
case 6:
{
lean_object* v___x_2603_; 
lean_dec(v_attrName_2460_);
lean_dec(v_stx_2453_);
v___x_2603_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_2454_, v_declName_2455_, v_attrKind_2456_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2603_;
}
case 7:
{
lean_object* v___x_2604_; 
lean_dec(v_attrName_2460_);
lean_dec(v_stx_2453_);
v___x_2604_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2454_, v_declName_2455_, v_attrKind_2456_, v___y_2463_, v___y_2464_);
return v___x_2604_;
}
case 8:
{
uint8_t v_post_2605_; uint8_t v_inv_2606_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___x_2615_; uint8_t v___x_2616_; 
lean_dec_ref(v_ext_2454_);
lean_dec(v_stx_2453_);
v_post_2605_ = lean_ctor_get_uint8(v_a_2495_, 0);
v_inv_2606_ = lean_ctor_get_uint8(v_a_2495_, 1);
lean_dec_ref(v_a_2495_);
v___x_2615_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2616_ = lean_name_eq(v_attrName_2460_, v___x_2615_);
lean_dec(v_attrName_2460_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
lean_dec(v_declName_2455_);
v___x_2617_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13);
v___x_2618_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2617_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2618_;
}
else
{
v___y_2608_ = v___y_2461_;
v___y_2609_ = v___y_2462_;
v___y_2610_ = v___y_2463_;
v___y_2611_ = v___y_2464_;
goto v___jp_2607_;
}
v___jp_2607_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
v___x_2612_ = l_Lean_Meta_Grind_normExt;
v___x_2613_ = lean_unsigned_to_nat(1000u);
v___x_2614_ = l_Lean_Meta_addSimpTheorem(v___x_2612_, v_declName_2455_, v_post_2605_, v_inv_2606_, v_attrKind_2456_, v___x_2613_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
return v___x_2614_;
}
}
default: 
{
lean_object* v___x_2619_; uint8_t v___x_2620_; 
lean_dec_ref(v_ext_2454_);
lean_dec(v_stx_2453_);
v___x_2619_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2620_ = lean_name_eq(v_attrName_2460_, v___x_2619_);
lean_dec(v_attrName_2460_);
if (v___x_2620_ == 0)
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
lean_dec(v_declName_2455_);
v___x_2621_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15);
v___x_2622_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2621_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2622_;
}
else
{
v___y_2467_ = v___y_2461_;
v___y_2468_ = v___y_2462_;
v___y_2469_ = v___y_2463_;
v___y_2470_ = v___y_2464_;
goto v___jp_2466_;
}
}
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v_attrName_2460_);
lean_dec(v_declName_2455_);
lean_dec_ref(v_ext_2454_);
lean_dec(v_stx_2453_);
v_a_2623_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2494_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2494_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
v___jp_2466_:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = l_Lean_Meta_Grind_normExt;
v___x_2472_ = lean_unsigned_to_nat(1000u);
v___x_2473_ = l_Lean_Meta_addDeclToUnfold(v___x_2471_, v_declName_2455_, v___x_2459_, v___x_2459_, v___x_2472_, v_attrKind_2456_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2485_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2476_ = v___x_2473_;
v_isShared_2477_ = v_isSharedCheck_2485_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2473_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2485_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
uint8_t v___x_2478_; 
v___x_2478_ = lean_unbox(v_a_2474_);
lean_dec(v_a_2474_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_del_object(v___x_2476_);
v___x_2479_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_2480_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2479_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
return v___x_2480_;
}
else
{
lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2481_ = lean_box(0);
if (v_isShared_2477_ == 0)
{
lean_ctor_set(v___x_2476_, 0, v___x_2481_);
v___x_2483_ = v___x_2476_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
v_a_2486_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2473_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2473_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_stx_2631_, lean_object* v_ext_2632_, lean_object* v_declName_2633_, lean_object* v_attrKind_2634_, lean_object* v_showInfo_2635_, lean_object* v_minIndexable_2636_, lean_object* v___x_2637_, lean_object* v_attrName_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
uint8_t v_attrKind_boxed_2644_; uint8_t v_showInfo_boxed_2645_; uint8_t v_minIndexable_boxed_2646_; uint8_t v___x_15358__boxed_2647_; lean_object* v_res_2648_; 
v_attrKind_boxed_2644_ = lean_unbox(v_attrKind_2634_);
v_showInfo_boxed_2645_ = lean_unbox(v_showInfo_2635_);
v_minIndexable_boxed_2646_ = lean_unbox(v_minIndexable_2636_);
v___x_15358__boxed_2647_ = lean_unbox(v___x_2637_);
v_res_2648_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_stx_2631_, v_ext_2632_, v_declName_2633_, v_attrKind_boxed_2644_, v_showInfo_boxed_2645_, v_minIndexable_boxed_2646_, v___x_15358__boxed_2647_, v_attrName_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
return v_res_2648_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2649_; double v___x_2650_; 
v___x_2649_ = lean_unsigned_to_nat(0u);
v___x_2650_ = lean_float_of_nat(v___x_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object* v_cls_2654_, lean_object* v_msg_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_ref_2661_; lean_object* v___x_2662_; lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2708_; 
v_ref_2661_ = lean_ctor_get(v___y_2658_, 5);
v___x_2662_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2665_ = v___x_2662_;
v_isShared_2666_ = v_isSharedCheck_2708_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2662_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2708_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2667_; lean_object* v_traceState_2668_; lean_object* v_env_2669_; lean_object* v_nextMacroScope_2670_; lean_object* v_ngen_2671_; lean_object* v_auxDeclNGen_2672_; lean_object* v_cache_2673_; lean_object* v_messages_2674_; lean_object* v_infoState_2675_; lean_object* v_snapshotTasks_2676_; lean_object* v_newDecls_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2707_; 
v___x_2667_ = lean_st_ref_take(v___y_2659_);
v_traceState_2668_ = lean_ctor_get(v___x_2667_, 4);
v_env_2669_ = lean_ctor_get(v___x_2667_, 0);
v_nextMacroScope_2670_ = lean_ctor_get(v___x_2667_, 1);
v_ngen_2671_ = lean_ctor_get(v___x_2667_, 2);
v_auxDeclNGen_2672_ = lean_ctor_get(v___x_2667_, 3);
v_cache_2673_ = lean_ctor_get(v___x_2667_, 5);
v_messages_2674_ = lean_ctor_get(v___x_2667_, 6);
v_infoState_2675_ = lean_ctor_get(v___x_2667_, 7);
v_snapshotTasks_2676_ = lean_ctor_get(v___x_2667_, 8);
v_newDecls_2677_ = lean_ctor_get(v___x_2667_, 9);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2707_ == 0)
{
v___x_2679_ = v___x_2667_;
v_isShared_2680_ = v_isSharedCheck_2707_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_newDecls_2677_);
lean_inc(v_snapshotTasks_2676_);
lean_inc(v_infoState_2675_);
lean_inc(v_messages_2674_);
lean_inc(v_cache_2673_);
lean_inc(v_traceState_2668_);
lean_inc(v_auxDeclNGen_2672_);
lean_inc(v_ngen_2671_);
lean_inc(v_nextMacroScope_2670_);
lean_inc(v_env_2669_);
lean_dec(v___x_2667_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2707_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
uint64_t v_tid_2681_; lean_object* v_traces_2682_; lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2706_; 
v_tid_2681_ = lean_ctor_get_uint64(v_traceState_2668_, sizeof(void*)*1);
v_traces_2682_ = lean_ctor_get(v_traceState_2668_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v_traceState_2668_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2684_ = v_traceState_2668_;
v_isShared_2685_ = v_isSharedCheck_2706_;
goto v_resetjp_2683_;
}
else
{
lean_inc(v_traces_2682_);
lean_dec(v_traceState_2668_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2706_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2686_; double v___x_2687_; uint8_t v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2696_; 
v___x_2686_ = lean_box(0);
v___x_2687_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_2688_ = 0;
v___x_2689_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2690_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2690_, 0, v_cls_2654_);
lean_ctor_set(v___x_2690_, 1, v___x_2686_);
lean_ctor_set(v___x_2690_, 2, v___x_2689_);
lean_ctor_set_float(v___x_2690_, sizeof(void*)*3, v___x_2687_);
lean_ctor_set_float(v___x_2690_, sizeof(void*)*3 + 8, v___x_2687_);
lean_ctor_set_uint8(v___x_2690_, sizeof(void*)*3 + 16, v___x_2688_);
v___x_2691_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_2692_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2690_);
lean_ctor_set(v___x_2692_, 1, v_a_2663_);
lean_ctor_set(v___x_2692_, 2, v___x_2691_);
lean_inc(v_ref_2661_);
v___x_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2693_, 0, v_ref_2661_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = l_Lean_PersistentArray_push___redArg(v_traces_2682_, v___x_2693_);
if (v_isShared_2685_ == 0)
{
lean_ctor_set(v___x_2684_, 0, v___x_2694_);
v___x_2696_ = v___x_2684_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2694_);
lean_ctor_set_uint64(v_reuseFailAlloc_2705_, sizeof(void*)*1, v_tid_2681_);
v___x_2696_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2698_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 4, v___x_2696_);
v___x_2698_ = v___x_2679_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_env_2669_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v_nextMacroScope_2670_);
lean_ctor_set(v_reuseFailAlloc_2704_, 2, v_ngen_2671_);
lean_ctor_set(v_reuseFailAlloc_2704_, 3, v_auxDeclNGen_2672_);
lean_ctor_set(v_reuseFailAlloc_2704_, 4, v___x_2696_);
lean_ctor_set(v_reuseFailAlloc_2704_, 5, v_cache_2673_);
lean_ctor_set(v_reuseFailAlloc_2704_, 6, v_messages_2674_);
lean_ctor_set(v_reuseFailAlloc_2704_, 7, v_infoState_2675_);
lean_ctor_set(v_reuseFailAlloc_2704_, 8, v_snapshotTasks_2676_);
lean_ctor_set(v_reuseFailAlloc_2704_, 9, v_newDecls_2677_);
v___x_2698_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2702_; 
v___x_2699_ = lean_st_ref_set(v___y_2659_, v___x_2698_);
v___x_2700_ = lean_box(0);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 0, v___x_2700_);
v___x_2702_ = v___x_2665_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v___x_2700_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object* v_cls_2709_, lean_object* v_msg_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2709_, v_msg_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
return v_res_2716_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_keys_2717_, lean_object* v_i_2718_, lean_object* v_k_2719_){
_start:
{
lean_object* v___x_2720_; uint8_t v___x_2721_; 
v___x_2720_ = lean_array_get_size(v_keys_2717_);
v___x_2721_ = lean_nat_dec_lt(v_i_2718_, v___x_2720_);
if (v___x_2721_ == 0)
{
lean_dec(v_i_2718_);
return v___x_2721_;
}
else
{
lean_object* v_k_x27_2722_; uint8_t v___x_2723_; 
v_k_x27_2722_ = lean_array_fget_borrowed(v_keys_2717_, v_i_2718_);
v___x_2723_ = l_Lean_instBEqExtraModUse_beq(v_k_2719_, v_k_x27_2722_);
if (v___x_2723_ == 0)
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
v___x_2724_ = lean_unsigned_to_nat(1u);
v___x_2725_ = lean_nat_add(v_i_2718_, v___x_2724_);
lean_dec(v_i_2718_);
v_i_2718_ = v___x_2725_;
goto _start;
}
else
{
lean_dec(v_i_2718_);
return v___x_2723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_keys_2727_, lean_object* v_i_2728_, lean_object* v_k_2729_){
_start:
{
uint8_t v_res_2730_; lean_object* v_r_2731_; 
v_res_2730_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_2727_, v_i_2728_, v_k_2729_);
lean_dec_ref(v_k_2729_);
lean_dec_ref(v_keys_2727_);
v_r_2731_ = lean_box(v_res_2730_);
return v_r_2731_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2732_, size_t v_x_2733_, lean_object* v_x_2734_){
_start:
{
if (lean_obj_tag(v_x_2732_) == 0)
{
lean_object* v_es_2735_; lean_object* v___x_2736_; size_t v___x_2737_; size_t v___x_2738_; size_t v___x_2739_; lean_object* v_j_2740_; lean_object* v___x_2741_; 
v_es_2735_ = lean_ctor_get(v_x_2732_, 0);
v___x_2736_ = lean_box(2);
v___x_2737_ = ((size_t)5ULL);
v___x_2738_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1);
v___x_2739_ = lean_usize_land(v_x_2733_, v___x_2738_);
v_j_2740_ = lean_usize_to_nat(v___x_2739_);
v___x_2741_ = lean_array_get_borrowed(v___x_2736_, v_es_2735_, v_j_2740_);
lean_dec(v_j_2740_);
switch(lean_obj_tag(v___x_2741_))
{
case 0:
{
lean_object* v_key_2742_; uint8_t v___x_2743_; 
v_key_2742_ = lean_ctor_get(v___x_2741_, 0);
v___x_2743_ = l_Lean_instBEqExtraModUse_beq(v_x_2734_, v_key_2742_);
return v___x_2743_;
}
case 1:
{
lean_object* v_node_2744_; size_t v___x_2745_; 
v_node_2744_ = lean_ctor_get(v___x_2741_, 0);
v___x_2745_ = lean_usize_shift_right(v_x_2733_, v___x_2737_);
v_x_2732_ = v_node_2744_;
v_x_2733_ = v___x_2745_;
goto _start;
}
default: 
{
uint8_t v___x_2747_; 
v___x_2747_ = 0;
return v___x_2747_;
}
}
}
else
{
lean_object* v_ks_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v_ks_2748_ = lean_ctor_get(v_x_2732_, 0);
v___x_2749_ = lean_unsigned_to_nat(0u);
v___x_2750_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_ks_2748_, v___x_2749_, v_x_2734_);
return v___x_2750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_){
_start:
{
size_t v_x_15858__boxed_2754_; uint8_t v_res_2755_; lean_object* v_r_2756_; 
v_x_15858__boxed_2754_ = lean_unbox_usize(v_x_2752_);
lean_dec(v_x_2752_);
v_res_2755_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2751_, v_x_15858__boxed_2754_, v_x_2753_);
lean_dec_ref(v_x_2753_);
lean_dec_ref(v_x_2751_);
v_r_2756_ = lean_box(v_res_2755_);
return v_r_2756_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2757_, lean_object* v_x_2758_){
_start:
{
uint64_t v___x_2759_; size_t v___x_2760_; uint8_t v___x_2761_; 
v___x_2759_ = l_Lean_instHashableExtraModUse_hash(v_x_2758_);
v___x_2760_ = lean_uint64_to_usize(v___x_2759_);
v___x_2761_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2757_, v___x_2760_, v_x_2758_);
return v___x_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_2762_, lean_object* v_x_2763_){
_start:
{
uint8_t v_res_2764_; lean_object* v_r_2765_; 
v_res_2764_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_2762_, v_x_2763_);
lean_dec_ref(v_x_2763_);
lean_dec_ref(v_x_2762_);
v_r_2765_ = lean_box(v_res_2764_);
return v_r_2765_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2768_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1));
v___x_2769_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0));
v___x_2770_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2769_, v___x_2768_);
return v___x_2770_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2775_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5));
v___x_2776_ = l_Lean_stringToMessageData(v___x_2775_);
return v___x_2776_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7));
v___x_2779_ = l_Lean_stringToMessageData(v___x_2778_);
return v___x_2779_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9(void){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2781_ = l_Lean_stringToMessageData(v___x_2780_);
return v___x_2781_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v_cls_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v_cls_2785_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_2786_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11));
v___x_2787_ = l_Lean_Name_append(v___x_2786_, v_cls_2785_);
return v___x_2787_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13));
v___x_2790_ = l_Lean_stringToMessageData(v___x_2789_);
return v___x_2790_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16(void){
_start:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___x_2793_ = l_Lean_stringToMessageData(v___x_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v_mod_2798_, uint8_t v_isMeta_2799_, lean_object* v_hint_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v___x_2806_; lean_object* v_env_2807_; uint8_t v_isExporting_2808_; lean_object* v___x_2809_; lean_object* v_env_2810_; lean_object* v___x_2811_; lean_object* v_entry_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___x_2859_; uint8_t v___x_2860_; 
v___x_2806_ = lean_st_ref_get(v___y_2804_);
v_env_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc_ref(v_env_2807_);
lean_dec(v___x_2806_);
v_isExporting_2808_ = lean_ctor_get_uint8(v_env_2807_, sizeof(void*)*8);
lean_dec_ref(v_env_2807_);
v___x_2809_ = lean_st_ref_get(v___y_2804_);
v_env_2810_ = lean_ctor_get(v___x_2809_, 0);
lean_inc_ref(v_env_2810_);
lean_dec(v___x_2809_);
v___x_2811_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_2798_);
v_entry_2812_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2812_, 0, v_mod_2798_);
lean_ctor_set_uint8(v_entry_2812_, sizeof(void*)*1, v_isExporting_2808_);
lean_ctor_set_uint8(v_entry_2812_, sizeof(void*)*1 + 1, v_isMeta_2799_);
v___x_2813_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2814_ = lean_box(1);
v___x_2815_ = lean_box(0);
v___x_2859_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2811_, v___x_2813_, v_env_2810_, v___x_2814_, v___x_2815_);
v___x_2860_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_2859_, v_entry_2812_);
lean_dec(v___x_2859_);
if (v___x_2860_ == 0)
{
lean_object* v_options_2861_; uint8_t v_hasTrace_2862_; 
v_options_2861_ = lean_ctor_get(v___y_2803_, 2);
v_hasTrace_2862_ = lean_ctor_get_uint8(v_options_2861_, sizeof(void*)*1);
if (v_hasTrace_2862_ == 0)
{
lean_dec(v_hint_2800_);
lean_dec(v_mod_2798_);
v___y_2817_ = v___y_2802_;
v___y_2818_ = v___y_2804_;
goto v___jp_2816_;
}
else
{
lean_object* v_inheritedTraceOptions_2863_; lean_object* v_cls_2864_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2871_; lean_object* v___y_2872_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v_inheritedTraceOptions_2863_ = lean_ctor_get(v___y_2803_, 13);
v_cls_2864_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_2884_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
v___x_2885_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2863_, v_options_2861_, v___x_2884_);
if (v___x_2885_ == 0)
{
lean_dec(v_hint_2800_);
lean_dec(v_mod_2798_);
v___y_2817_ = v___y_2802_;
v___y_2818_ = v___y_2804_;
goto v___jp_2816_;
}
else
{
lean_object* v___x_2886_; lean_object* v___y_2888_; 
v___x_2886_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
if (v_isExporting_2808_ == 0)
{
lean_object* v___x_2895_; 
v___x_2895_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19));
v___y_2888_ = v___x_2895_;
goto v___jp_2887_;
}
else
{
lean_object* v___x_2896_; 
v___x_2896_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20));
v___y_2888_ = v___x_2896_;
goto v___jp_2887_;
}
v___jp_2887_:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; 
lean_inc_ref(v___y_2888_);
v___x_2889_ = l_Lean_stringToMessageData(v___y_2888_);
v___x_2890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2890_, 0, v___x_2886_);
lean_ctor_set(v___x_2890_, 1, v___x_2889_);
v___x_2891_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16);
v___x_2892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2890_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
if (v_isMeta_2799_ == 0)
{
lean_object* v___x_2893_; 
v___x_2893_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_2871_ = v___x_2892_;
v___y_2872_ = v___x_2893_;
goto v___jp_2870_;
}
else
{
lean_object* v___x_2894_; 
v___x_2894_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_2871_ = v___x_2892_;
v___y_2872_ = v___x_2894_;
goto v___jp_2870_;
}
}
}
v___jp_2865_:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___y_2866_);
lean_ctor_set(v___x_2868_, 1, v___y_2867_);
v___x_2869_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2864_, v___x_2868_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_dec_ref(v___x_2869_);
v___y_2817_ = v___y_2802_;
v___y_2818_ = v___y_2804_;
goto v___jp_2816_;
}
else
{
lean_dec_ref(v_entry_2812_);
return v___x_2869_;
}
}
v___jp_2870_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; 
lean_inc_ref(v___y_2872_);
v___x_2873_ = l_Lean_stringToMessageData(v___y_2872_);
v___x_2874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___y_2871_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_2876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2874_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
v___x_2877_ = l_Lean_MessageData_ofName(v_mod_2798_);
v___x_2878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2876_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
v___x_2879_ = l_Lean_Name_isAnonymous(v_hint_2800_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2880_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_2881_ = l_Lean_MessageData_ofName(v_hint_2800_);
v___x_2882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2882_, 0, v___x_2880_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
v___y_2866_ = v___x_2878_;
v___y_2867_ = v___x_2882_;
goto v___jp_2865_;
}
else
{
lean_object* v___x_2883_; 
lean_dec(v_hint_2800_);
v___x_2883_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_2866_ = v___x_2878_;
v___y_2867_ = v___x_2883_;
goto v___jp_2865_;
}
}
}
}
else
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
lean_dec_ref(v_entry_2812_);
lean_dec(v_hint_2800_);
lean_dec(v_mod_2798_);
v___x_2897_ = lean_box(0);
v___x_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2898_, 0, v___x_2897_);
return v___x_2898_;
}
v___jp_2816_:
{
lean_object* v___x_2819_; lean_object* v_toEnvExtension_2820_; lean_object* v_env_2821_; lean_object* v_nextMacroScope_2822_; lean_object* v_ngen_2823_; lean_object* v_auxDeclNGen_2824_; lean_object* v_traceState_2825_; lean_object* v_messages_2826_; lean_object* v_infoState_2827_; lean_object* v_snapshotTasks_2828_; lean_object* v_newDecls_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2857_; 
v___x_2819_ = lean_st_ref_take(v___y_2818_);
v_toEnvExtension_2820_ = lean_ctor_get(v___x_2813_, 0);
v_env_2821_ = lean_ctor_get(v___x_2819_, 0);
v_nextMacroScope_2822_ = lean_ctor_get(v___x_2819_, 1);
v_ngen_2823_ = lean_ctor_get(v___x_2819_, 2);
v_auxDeclNGen_2824_ = lean_ctor_get(v___x_2819_, 3);
v_traceState_2825_ = lean_ctor_get(v___x_2819_, 4);
v_messages_2826_ = lean_ctor_get(v___x_2819_, 6);
v_infoState_2827_ = lean_ctor_get(v___x_2819_, 7);
v_snapshotTasks_2828_ = lean_ctor_get(v___x_2819_, 8);
v_newDecls_2829_ = lean_ctor_get(v___x_2819_, 9);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; 
v_unused_2858_ = lean_ctor_get(v___x_2819_, 5);
lean_dec(v_unused_2858_);
v___x_2831_ = v___x_2819_;
v_isShared_2832_ = v_isSharedCheck_2857_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_newDecls_2829_);
lean_inc(v_snapshotTasks_2828_);
lean_inc(v_infoState_2827_);
lean_inc(v_messages_2826_);
lean_inc(v_traceState_2825_);
lean_inc(v_auxDeclNGen_2824_);
lean_inc(v_ngen_2823_);
lean_inc(v_nextMacroScope_2822_);
lean_inc(v_env_2821_);
lean_dec(v___x_2819_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2857_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v_asyncMode_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2837_; 
v_asyncMode_2833_ = lean_ctor_get(v_toEnvExtension_2820_, 2);
v___x_2834_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2813_, v_env_2821_, v_entry_2812_, v_asyncMode_2833_, v___x_2815_);
v___x_2835_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 5, v___x_2835_);
lean_ctor_set(v___x_2831_, 0, v___x_2834_);
v___x_2837_ = v___x_2831_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_nextMacroScope_2822_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v_ngen_2823_);
lean_ctor_set(v_reuseFailAlloc_2856_, 3, v_auxDeclNGen_2824_);
lean_ctor_set(v_reuseFailAlloc_2856_, 4, v_traceState_2825_);
lean_ctor_set(v_reuseFailAlloc_2856_, 5, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2856_, 6, v_messages_2826_);
lean_ctor_set(v_reuseFailAlloc_2856_, 7, v_infoState_2827_);
lean_ctor_set(v_reuseFailAlloc_2856_, 8, v_snapshotTasks_2828_);
lean_ctor_set(v_reuseFailAlloc_2856_, 9, v_newDecls_2829_);
v___x_2837_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v_mctx_2840_; lean_object* v_zetaDeltaFVarIds_2841_; lean_object* v_postponed_2842_; lean_object* v_diag_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2854_; 
v___x_2838_ = lean_st_ref_set(v___y_2818_, v___x_2837_);
v___x_2839_ = lean_st_ref_take(v___y_2817_);
v_mctx_2840_ = lean_ctor_get(v___x_2839_, 0);
v_zetaDeltaFVarIds_2841_ = lean_ctor_get(v___x_2839_, 2);
v_postponed_2842_ = lean_ctor_get(v___x_2839_, 3);
v_diag_2843_ = lean_ctor_get(v___x_2839_, 4);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2854_ == 0)
{
lean_object* v_unused_2855_; 
v_unused_2855_ = lean_ctor_get(v___x_2839_, 1);
lean_dec(v_unused_2855_);
v___x_2845_ = v___x_2839_;
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_diag_2843_);
lean_inc(v_postponed_2842_);
lean_inc(v_zetaDeltaFVarIds_2841_);
lean_inc(v_mctx_2840_);
lean_dec(v___x_2839_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; lean_object* v___x_2849_; 
v___x_2847_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 1, v___x_2847_);
v___x_2849_ = v___x_2845_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_mctx_2840_);
lean_ctor_set(v_reuseFailAlloc_2853_, 1, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2853_, 2, v_zetaDeltaFVarIds_2841_);
lean_ctor_set(v_reuseFailAlloc_2853_, 3, v_postponed_2842_);
lean_ctor_set(v_reuseFailAlloc_2853_, 4, v_diag_2843_);
v___x_2849_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2850_ = lean_st_ref_set(v___y_2817_, v___x_2849_);
v___x_2851_ = lean_box(0);
v___x_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2852_, 0, v___x_2851_);
return v___x_2852_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v_mod_2899_, lean_object* v_isMeta_2900_, lean_object* v_hint_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
uint8_t v_isMeta_boxed_2907_; lean_object* v_res_2908_; 
v_isMeta_boxed_2907_ = lean_unbox(v_isMeta_2900_);
v_res_2908_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_mod_2899_, v_isMeta_boxed_2907_, v_hint_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object* v_a_2909_, lean_object* v_x_2910_){
_start:
{
if (lean_obj_tag(v_x_2910_) == 0)
{
lean_object* v___x_2911_; 
v___x_2911_ = lean_box(0);
return v___x_2911_;
}
else
{
lean_object* v_key_2912_; lean_object* v_value_2913_; lean_object* v_tail_2914_; uint8_t v___x_2915_; 
v_key_2912_ = lean_ctor_get(v_x_2910_, 0);
v_value_2913_ = lean_ctor_get(v_x_2910_, 1);
v_tail_2914_ = lean_ctor_get(v_x_2910_, 2);
v___x_2915_ = lean_name_eq(v_key_2912_, v_a_2909_);
if (v___x_2915_ == 0)
{
v_x_2910_ = v_tail_2914_;
goto _start;
}
else
{
lean_object* v___x_2917_; 
lean_inc(v_value_2913_);
v___x_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2917_, 0, v_value_2913_);
return v___x_2917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_a_2918_, lean_object* v_x_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2918_, v_x_2919_);
lean_dec(v_x_2919_);
lean_dec(v_a_2918_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object* v_m_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v_buckets_2923_; lean_object* v___x_2924_; uint64_t v___y_2926_; 
v_buckets_2923_ = lean_ctor_get(v_m_2921_, 1);
v___x_2924_ = lean_array_get_size(v_buckets_2923_);
if (lean_obj_tag(v_a_2922_) == 0)
{
uint64_t v___x_2940_; 
v___x_2940_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_2926_ = v___x_2940_;
goto v___jp_2925_;
}
else
{
uint64_t v_hash_2941_; 
v_hash_2941_ = lean_ctor_get_uint64(v_a_2922_, sizeof(void*)*2);
v___y_2926_ = v_hash_2941_;
goto v___jp_2925_;
}
v___jp_2925_:
{
uint64_t v___x_2927_; uint64_t v___x_2928_; uint64_t v_fold_2929_; uint64_t v___x_2930_; uint64_t v___x_2931_; uint64_t v___x_2932_; size_t v___x_2933_; size_t v___x_2934_; size_t v___x_2935_; size_t v___x_2936_; size_t v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2927_ = 32ULL;
v___x_2928_ = lean_uint64_shift_right(v___y_2926_, v___x_2927_);
v_fold_2929_ = lean_uint64_xor(v___y_2926_, v___x_2928_);
v___x_2930_ = 16ULL;
v___x_2931_ = lean_uint64_shift_right(v_fold_2929_, v___x_2930_);
v___x_2932_ = lean_uint64_xor(v_fold_2929_, v___x_2931_);
v___x_2933_ = lean_uint64_to_usize(v___x_2932_);
v___x_2934_ = lean_usize_of_nat(v___x_2924_);
v___x_2935_ = ((size_t)1ULL);
v___x_2936_ = lean_usize_sub(v___x_2934_, v___x_2935_);
v___x_2937_ = lean_usize_land(v___x_2933_, v___x_2936_);
v___x_2938_ = lean_array_uget_borrowed(v_buckets_2923_, v___x_2937_);
v___x_2939_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2922_, v___x_2938_);
return v___x_2939_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object* v_m_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v_res_2944_; 
v_res_2944_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_2942_, v_a_2943_);
lean_dec(v_a_2943_);
lean_dec_ref(v_m_2942_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v___x_2945_, lean_object* v_declName_2946_, lean_object* v_as_2947_, size_t v_sz_2948_, size_t v_i_2949_, lean_object* v_b_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
uint8_t v___x_2956_; 
v___x_2956_ = lean_usize_dec_lt(v_i_2949_, v_sz_2948_);
if (v___x_2956_ == 0)
{
lean_object* v___x_2957_; 
lean_dec(v_declName_2946_);
v___x_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2957_, 0, v_b_2950_);
return v___x_2957_;
}
else
{
lean_object* v___x_2958_; lean_object* v_modules_2959_; lean_object* v___x_2960_; lean_object* v_a_2961_; lean_object* v___x_2962_; lean_object* v_toImport_2963_; lean_object* v_module_2964_; uint8_t v___x_2965_; lean_object* v___x_2966_; 
v___x_2958_ = l_Lean_Environment_header(v___x_2945_);
v_modules_2959_ = lean_ctor_get(v___x_2958_, 3);
lean_inc_ref(v_modules_2959_);
lean_dec_ref(v___x_2958_);
v___x_2960_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2961_ = lean_array_uget_borrowed(v_as_2947_, v_i_2949_);
v___x_2962_ = lean_array_get(v___x_2960_, v_modules_2959_, v_a_2961_);
lean_dec_ref(v_modules_2959_);
v_toImport_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc_ref(v_toImport_2963_);
lean_dec(v___x_2962_);
v_module_2964_ = lean_ctor_get(v_toImport_2963_, 0);
lean_inc(v_module_2964_);
lean_dec_ref(v_toImport_2963_);
v___x_2965_ = 0;
lean_inc(v_declName_2946_);
v___x_2966_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_2964_, v___x_2965_, v_declName_2946_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v___x_2967_; size_t v___x_2968_; size_t v___x_2969_; 
lean_dec_ref(v___x_2966_);
v___x_2967_ = lean_box(0);
v___x_2968_ = ((size_t)1ULL);
v___x_2969_ = lean_usize_add(v_i_2949_, v___x_2968_);
v_i_2949_ = v___x_2969_;
v_b_2950_ = v___x_2967_;
goto _start;
}
else
{
lean_dec(v_declName_2946_);
return v___x_2966_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v___x_2971_, lean_object* v_declName_2972_, lean_object* v_as_2973_, lean_object* v_sz_2974_, lean_object* v_i_2975_, lean_object* v_b_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
size_t v_sz_boxed_2982_; size_t v_i_boxed_2983_; lean_object* v_res_2984_; 
v_sz_boxed_2982_ = lean_unbox_usize(v_sz_2974_);
lean_dec(v_sz_2974_);
v_i_boxed_2983_ = lean_unbox_usize(v_i_2975_);
lean_dec(v_i_2975_);
v_res_2984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v___x_2971_, v_declName_2972_, v_as_2973_, v_sz_boxed_2982_, v_i_boxed_2983_, v_b_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec_ref(v_as_2973_);
lean_dec_ref(v___x_2971_);
return v_res_2984_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___x_2988_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0));
v___x_2989_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2988_, v___x_2987_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_2992_, uint8_t v_isMeta_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_){
_start:
{
lean_object* v___x_2999_; lean_object* v_env_3003_; lean_object* v___y_3005_; lean_object* v___x_3018_; 
v___x_2999_ = lean_st_ref_get(v___y_2997_);
v_env_3003_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_ref(v_env_3003_);
lean_dec(v___x_2999_);
v___x_3018_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3003_, v_declName_2992_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_dec_ref(v_env_3003_);
lean_dec(v_declName_2992_);
goto v___jp_3000_;
}
else
{
lean_object* v_val_3019_; lean_object* v___x_3020_; lean_object* v_modules_3021_; lean_object* v___x_3022_; uint8_t v___x_3023_; 
v_val_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_val_3019_);
lean_dec_ref(v___x_3018_);
v___x_3020_ = l_Lean_Environment_header(v_env_3003_);
v_modules_3021_ = lean_ctor_get(v___x_3020_, 3);
lean_inc_ref(v_modules_3021_);
lean_dec_ref(v___x_3020_);
v___x_3022_ = lean_array_get_size(v_modules_3021_);
v___x_3023_ = lean_nat_dec_lt(v_val_3019_, v___x_3022_);
if (v___x_3023_ == 0)
{
lean_dec_ref(v_modules_3021_);
lean_dec(v_val_3019_);
lean_dec_ref(v_env_3003_);
lean_dec(v_declName_2992_);
goto v___jp_3000_;
}
else
{
lean_object* v___x_3024_; lean_object* v_env_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; uint8_t v___y_3029_; 
v___x_3024_ = lean_st_ref_get(v___y_2997_);
v_env_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc_ref(v_env_3025_);
lean_dec(v___x_3024_);
v___x_3026_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3027_ = lean_array_fget(v_modules_3021_, v_val_3019_);
lean_dec(v_val_3019_);
lean_dec_ref(v_modules_3021_);
if (v_isMeta_2993_ == 0)
{
lean_dec_ref(v_env_3025_);
v___y_3029_ = v_isMeta_2993_;
goto v___jp_3028_;
}
else
{
uint8_t v___x_3040_; 
lean_inc(v_declName_2992_);
v___x_3040_ = l_Lean_isMarkedMeta(v_env_3025_, v_declName_2992_);
if (v___x_3040_ == 0)
{
v___y_3029_ = v_isMeta_2993_;
goto v___jp_3028_;
}
else
{
uint8_t v___x_3041_; 
v___x_3041_ = 0;
v___y_3029_ = v___x_3041_;
goto v___jp_3028_;
}
}
v___jp_3028_:
{
lean_object* v_toImport_3030_; lean_object* v_module_3031_; lean_object* v___x_3032_; 
v_toImport_3030_ = lean_ctor_get(v___x_3027_, 0);
lean_inc_ref(v_toImport_3030_);
lean_dec(v___x_3027_);
v_module_3031_ = lean_ctor_get(v_toImport_3030_, 0);
lean_inc(v_module_3031_);
lean_dec_ref(v_toImport_3030_);
lean_inc(v_declName_2992_);
v___x_3032_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3031_, v___y_3029_, v_declName_2992_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
lean_dec_ref(v___x_3032_);
v___x_3033_ = l_Lean_indirectModUseExt;
v___x_3034_ = lean_box(1);
v___x_3035_ = lean_box(0);
lean_inc_ref(v_env_3003_);
v___x_3036_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3026_, v___x_3033_, v_env_3003_, v___x_3034_, v___x_3035_);
v___x_3037_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3036_, v_declName_2992_);
lean_dec(v___x_3036_);
if (lean_obj_tag(v___x_3037_) == 0)
{
lean_object* v___x_3038_; 
v___x_3038_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_3005_ = v___x_3038_;
goto v___jp_3004_;
}
else
{
lean_object* v_val_3039_; 
v_val_3039_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_val_3039_);
lean_dec_ref(v___x_3037_);
v___y_3005_ = v_val_3039_;
goto v___jp_3004_;
}
}
else
{
lean_dec_ref(v_env_3003_);
lean_dec(v_declName_2992_);
return v___x_3032_;
}
}
}
}
v___jp_3000_:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = lean_box(0);
v___x_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3002_, 0, v___x_3001_);
return v___x_3002_;
}
v___jp_3004_:
{
lean_object* v___x_3006_; size_t v_sz_3007_; size_t v___x_3008_; lean_object* v___x_3009_; 
v___x_3006_ = lean_box(0);
v_sz_3007_ = lean_array_size(v___y_3005_);
v___x_3008_ = ((size_t)0ULL);
v___x_3009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_env_3003_, v_declName_2992_, v___y_3005_, v_sz_3007_, v___x_3008_, v___x_3006_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
lean_dec_ref(v___y_3005_);
lean_dec_ref(v_env_3003_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3009_);
if (v_isSharedCheck_3016_ == 0)
{
lean_object* v_unused_3017_; 
v_unused_3017_ = lean_ctor_get(v___x_3009_, 0);
lean_dec(v_unused_3017_);
v___x_3011_ = v___x_3009_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_dec(v___x_3009_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 0, v___x_3006_);
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3006_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
else
{
return v___x_3009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_3042_, lean_object* v_isMeta_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
uint8_t v_isMeta_boxed_3049_; lean_object* v_res_3050_; 
v_isMeta_boxed_3049_ = lean_unbox(v_isMeta_3043_);
v_res_3050_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3042_, v_isMeta_boxed_3049_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object* v___y_3051_, uint8_t v_isExporting_3052_, lean_object* v___x_3053_, lean_object* v___y_3054_, lean_object* v___x_3055_, lean_object* v_a_x3f_3056_){
_start:
{
lean_object* v___x_3058_; lean_object* v_env_3059_; lean_object* v_nextMacroScope_3060_; lean_object* v_ngen_3061_; lean_object* v_auxDeclNGen_3062_; lean_object* v_traceState_3063_; lean_object* v_messages_3064_; lean_object* v_infoState_3065_; lean_object* v_snapshotTasks_3066_; lean_object* v_newDecls_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3092_; 
v___x_3058_ = lean_st_ref_take(v___y_3051_);
v_env_3059_ = lean_ctor_get(v___x_3058_, 0);
v_nextMacroScope_3060_ = lean_ctor_get(v___x_3058_, 1);
v_ngen_3061_ = lean_ctor_get(v___x_3058_, 2);
v_auxDeclNGen_3062_ = lean_ctor_get(v___x_3058_, 3);
v_traceState_3063_ = lean_ctor_get(v___x_3058_, 4);
v_messages_3064_ = lean_ctor_get(v___x_3058_, 6);
v_infoState_3065_ = lean_ctor_get(v___x_3058_, 7);
v_snapshotTasks_3066_ = lean_ctor_get(v___x_3058_, 8);
v_newDecls_3067_ = lean_ctor_get(v___x_3058_, 9);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3092_ == 0)
{
lean_object* v_unused_3093_; 
v_unused_3093_ = lean_ctor_get(v___x_3058_, 5);
lean_dec(v_unused_3093_);
v___x_3069_ = v___x_3058_;
v_isShared_3070_ = v_isSharedCheck_3092_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_newDecls_3067_);
lean_inc(v_snapshotTasks_3066_);
lean_inc(v_infoState_3065_);
lean_inc(v_messages_3064_);
lean_inc(v_traceState_3063_);
lean_inc(v_auxDeclNGen_3062_);
lean_inc(v_ngen_3061_);
lean_inc(v_nextMacroScope_3060_);
lean_inc(v_env_3059_);
lean_dec(v___x_3058_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3092_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3071_; lean_object* v___x_3073_; 
v___x_3071_ = l_Lean_Environment_setExporting(v_env_3059_, v_isExporting_3052_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 5, v___x_3053_);
lean_ctor_set(v___x_3069_, 0, v___x_3071_);
v___x_3073_ = v___x_3069_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3071_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_nextMacroScope_3060_);
lean_ctor_set(v_reuseFailAlloc_3091_, 2, v_ngen_3061_);
lean_ctor_set(v_reuseFailAlloc_3091_, 3, v_auxDeclNGen_3062_);
lean_ctor_set(v_reuseFailAlloc_3091_, 4, v_traceState_3063_);
lean_ctor_set(v_reuseFailAlloc_3091_, 5, v___x_3053_);
lean_ctor_set(v_reuseFailAlloc_3091_, 6, v_messages_3064_);
lean_ctor_set(v_reuseFailAlloc_3091_, 7, v_infoState_3065_);
lean_ctor_set(v_reuseFailAlloc_3091_, 8, v_snapshotTasks_3066_);
lean_ctor_set(v_reuseFailAlloc_3091_, 9, v_newDecls_3067_);
v___x_3073_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v_mctx_3076_; lean_object* v_zetaDeltaFVarIds_3077_; lean_object* v_postponed_3078_; lean_object* v_diag_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3089_; 
v___x_3074_ = lean_st_ref_set(v___y_3051_, v___x_3073_);
v___x_3075_ = lean_st_ref_take(v___y_3054_);
v_mctx_3076_ = lean_ctor_get(v___x_3075_, 0);
v_zetaDeltaFVarIds_3077_ = lean_ctor_get(v___x_3075_, 2);
v_postponed_3078_ = lean_ctor_get(v___x_3075_, 3);
v_diag_3079_ = lean_ctor_get(v___x_3075_, 4);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3089_ == 0)
{
lean_object* v_unused_3090_; 
v_unused_3090_ = lean_ctor_get(v___x_3075_, 1);
lean_dec(v_unused_3090_);
v___x_3081_ = v___x_3075_;
v_isShared_3082_ = v_isSharedCheck_3089_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_diag_3079_);
lean_inc(v_postponed_3078_);
lean_inc(v_zetaDeltaFVarIds_3077_);
lean_inc(v_mctx_3076_);
lean_dec(v___x_3075_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3089_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
lean_ctor_set(v___x_3081_, 1, v___x_3055_);
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_mctx_3076_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v___x_3055_);
lean_ctor_set(v_reuseFailAlloc_3088_, 2, v_zetaDeltaFVarIds_3077_);
lean_ctor_set(v_reuseFailAlloc_3088_, 3, v_postponed_3078_);
lean_ctor_set(v_reuseFailAlloc_3088_, 4, v_diag_3079_);
v___x_3084_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3085_ = lean_st_ref_set(v___y_3054_, v___x_3084_);
v___x_3086_ = lean_box(0);
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
return v___x_3087_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object* v___y_3094_, lean_object* v_isExporting_3095_, lean_object* v___x_3096_, lean_object* v___y_3097_, lean_object* v___x_3098_, lean_object* v_a_x3f_3099_, lean_object* v___y_3100_){
_start:
{
uint8_t v_isExporting_boxed_3101_; lean_object* v_res_3102_; 
v_isExporting_boxed_3101_ = lean_unbox(v_isExporting_3095_);
v_res_3102_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3094_, v_isExporting_boxed_3101_, v___x_3096_, v___y_3097_, v___x_3098_, v_a_x3f_3099_);
lean_dec(v_a_x3f_3099_);
lean_dec(v___y_3097_);
lean_dec(v___y_3094_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object* v_x_3103_, uint8_t v_isExporting_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v___x_3110_; lean_object* v_env_3111_; uint8_t v_isExporting_3112_; lean_object* v___x_3113_; lean_object* v_env_3114_; lean_object* v_nextMacroScope_3115_; lean_object* v_ngen_3116_; lean_object* v_auxDeclNGen_3117_; lean_object* v_traceState_3118_; lean_object* v_messages_3119_; lean_object* v_infoState_3120_; lean_object* v_snapshotTasks_3121_; lean_object* v_newDecls_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3176_; 
v___x_3110_ = lean_st_ref_get(v___y_3108_);
v_env_3111_ = lean_ctor_get(v___x_3110_, 0);
lean_inc_ref(v_env_3111_);
lean_dec(v___x_3110_);
v_isExporting_3112_ = lean_ctor_get_uint8(v_env_3111_, sizeof(void*)*8);
lean_dec_ref(v_env_3111_);
v___x_3113_ = lean_st_ref_take(v___y_3108_);
v_env_3114_ = lean_ctor_get(v___x_3113_, 0);
v_nextMacroScope_3115_ = lean_ctor_get(v___x_3113_, 1);
v_ngen_3116_ = lean_ctor_get(v___x_3113_, 2);
v_auxDeclNGen_3117_ = lean_ctor_get(v___x_3113_, 3);
v_traceState_3118_ = lean_ctor_get(v___x_3113_, 4);
v_messages_3119_ = lean_ctor_get(v___x_3113_, 6);
v_infoState_3120_ = lean_ctor_get(v___x_3113_, 7);
v_snapshotTasks_3121_ = lean_ctor_get(v___x_3113_, 8);
v_newDecls_3122_ = lean_ctor_get(v___x_3113_, 9);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; 
v_unused_3177_ = lean_ctor_get(v___x_3113_, 5);
lean_dec(v_unused_3177_);
v___x_3124_ = v___x_3113_;
v_isShared_3125_ = v_isSharedCheck_3176_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_newDecls_3122_);
lean_inc(v_snapshotTasks_3121_);
lean_inc(v_infoState_3120_);
lean_inc(v_messages_3119_);
lean_inc(v_traceState_3118_);
lean_inc(v_auxDeclNGen_3117_);
lean_inc(v_ngen_3116_);
lean_inc(v_nextMacroScope_3115_);
lean_inc(v_env_3114_);
lean_dec(v___x_3113_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3176_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3129_; 
v___x_3126_ = l_Lean_Environment_setExporting(v_env_3114_, v_isExporting_3104_);
v___x_3127_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 5, v___x_3127_);
lean_ctor_set(v___x_3124_, 0, v___x_3126_);
v___x_3129_ = v___x_3124_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3126_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v_nextMacroScope_3115_);
lean_ctor_set(v_reuseFailAlloc_3175_, 2, v_ngen_3116_);
lean_ctor_set(v_reuseFailAlloc_3175_, 3, v_auxDeclNGen_3117_);
lean_ctor_set(v_reuseFailAlloc_3175_, 4, v_traceState_3118_);
lean_ctor_set(v_reuseFailAlloc_3175_, 5, v___x_3127_);
lean_ctor_set(v_reuseFailAlloc_3175_, 6, v_messages_3119_);
lean_ctor_set(v_reuseFailAlloc_3175_, 7, v_infoState_3120_);
lean_ctor_set(v_reuseFailAlloc_3175_, 8, v_snapshotTasks_3121_);
lean_ctor_set(v_reuseFailAlloc_3175_, 9, v_newDecls_3122_);
v___x_3129_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v_mctx_3132_; lean_object* v_zetaDeltaFVarIds_3133_; lean_object* v_postponed_3134_; lean_object* v_diag_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3173_; 
v___x_3130_ = lean_st_ref_set(v___y_3108_, v___x_3129_);
v___x_3131_ = lean_st_ref_take(v___y_3106_);
v_mctx_3132_ = lean_ctor_get(v___x_3131_, 0);
v_zetaDeltaFVarIds_3133_ = lean_ctor_get(v___x_3131_, 2);
v_postponed_3134_ = lean_ctor_get(v___x_3131_, 3);
v_diag_3135_ = lean_ctor_get(v___x_3131_, 4);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3173_ == 0)
{
lean_object* v_unused_3174_; 
v_unused_3174_ = lean_ctor_get(v___x_3131_, 1);
lean_dec(v_unused_3174_);
v___x_3137_ = v___x_3131_;
v_isShared_3138_ = v_isSharedCheck_3173_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_diag_3135_);
lean_inc(v_postponed_3134_);
lean_inc(v_zetaDeltaFVarIds_3133_);
lean_inc(v_mctx_3132_);
lean_dec(v___x_3131_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3173_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3139_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 1, v___x_3139_);
v___x_3141_ = v___x_3137_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_mctx_3132_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3172_, 2, v_zetaDeltaFVarIds_3133_);
lean_ctor_set(v_reuseFailAlloc_3172_, 3, v_postponed_3134_);
lean_ctor_set(v_reuseFailAlloc_3172_, 4, v_diag_3135_);
v___x_3141_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; lean_object* v_r_3143_; 
v___x_3142_ = lean_st_ref_set(v___y_3106_, v___x_3141_);
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
lean_inc(v___y_3106_);
lean_inc_ref(v___y_3105_);
v_r_3143_ = lean_apply_5(v_x_3103_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, lean_box(0));
if (lean_obj_tag(v_r_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3160_; 
v_a_3144_ = lean_ctor_get(v_r_3143_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_r_3143_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3146_ = v_r_3143_;
v_isShared_3147_ = v_isSharedCheck_3160_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v_r_3143_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3160_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
lean_inc(v_a_3144_);
if (v_isShared_3147_ == 0)
{
lean_ctor_set_tag(v___x_3146_, 1);
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
lean_object* v___x_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
v___x_3150_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3108_, v_isExporting_3112_, v___x_3127_, v___y_3106_, v___x_3139_, v___x_3149_);
lean_dec_ref(v___x_3149_);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; 
v_unused_3158_ = lean_ctor_get(v___x_3150_, 0);
lean_dec(v_unused_3158_);
v___x_3152_ = v___x_3150_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_dec(v___x_3150_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 0, v_a_3144_);
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3144_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
else
{
lean_object* v_a_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3170_; 
v_a_3161_ = lean_ctor_get(v_r_3143_, 0);
lean_inc(v_a_3161_);
lean_dec_ref(v_r_3143_);
v___x_3162_ = lean_box(0);
v___x_3163_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3108_, v_isExporting_3112_, v___x_3127_, v___y_3106_, v___x_3139_, v___x_3162_);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; 
v_unused_3171_ = lean_ctor_get(v___x_3163_, 0);
lean_dec(v_unused_3171_);
v___x_3165_ = v___x_3163_;
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
else
{
lean_dec(v___x_3163_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3170_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3166_ == 0)
{
lean_ctor_set_tag(v___x_3165_, 1);
lean_ctor_set(v___x_3165_, 0, v_a_3161_);
v___x_3168_ = v___x_3165_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3161_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
return v___x_3168_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object* v_x_3178_, lean_object* v_isExporting_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
uint8_t v_isExporting_boxed_3185_; lean_object* v_res_3186_; 
v_isExporting_boxed_3185_ = lean_unbox(v_isExporting_3179_);
v_res_3186_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3178_, v_isExporting_boxed_3185_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
lean_dec_ref(v___y_3180_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_3187_, uint8_t v_when_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
if (v_when_3188_ == 0)
{
lean_object* v___x_3194_; 
lean_inc(v___y_3192_);
lean_inc_ref(v___y_3191_);
lean_inc(v___y_3190_);
lean_inc_ref(v___y_3189_);
v___x_3194_ = lean_apply_5(v_x_3187_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_, lean_box(0));
return v___x_3194_;
}
else
{
uint8_t v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = 0;
v___x_3196_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3187_, v___x_3195_, v___y_3189_, v___y_3190_, v___y_3191_, v___y_3192_);
return v___x_3196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_3197_, lean_object* v_when_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
uint8_t v_when_boxed_3204_; lean_object* v_res_3205_; 
v_when_boxed_3204_ = lean_unbox(v_when_3198_);
v_res_3205_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3197_, v_when_boxed_3204_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v___x_3206_, lean_object* v_ext_3207_, uint8_t v_showInfo_3208_, uint8_t v_minIndexable_3209_, lean_object* v_attrName_3210_, lean_object* v_declName_3211_, lean_object* v_stx_3212_, uint8_t v_attrKind_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
uint8_t v___x_3217_; uint8_t v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___y_3234_; lean_object* v___x_3244_; 
v___x_3217_ = 0;
v___x_3218_ = 1;
v___x_3219_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3220_ = lean_unsigned_to_nat(32u);
v___x_3221_ = lean_mk_empty_array_with_capacity(v___x_3220_);
lean_dec_ref(v___x_3221_);
v___x_3222_ = lean_unsigned_to_nat(0u);
v___x_3223_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_3224_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_3225_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6));
v___x_3226_ = lean_box(0);
lean_inc(v___x_3206_);
v___x_3227_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3227_, 0, v___x_3219_);
lean_ctor_set(v___x_3227_, 1, v___x_3206_);
lean_ctor_set(v___x_3227_, 2, v___x_3224_);
lean_ctor_set(v___x_3227_, 3, v___x_3225_);
lean_ctor_set(v___x_3227_, 4, v___x_3226_);
lean_ctor_set(v___x_3227_, 5, v___x_3222_);
lean_ctor_set(v___x_3227_, 6, v___x_3226_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*7, v___x_3217_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*7 + 1, v___x_3217_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*7 + 2, v___x_3217_);
lean_ctor_set_uint8(v___x_3227_, sizeof(void*)*7 + 3, v___x_3218_);
v___x_3228_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3229_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3230_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_3231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3228_);
lean_ctor_set(v___x_3231_, 1, v___x_3229_);
lean_ctor_set(v___x_3231_, 2, v___x_3206_);
lean_ctor_set(v___x_3231_, 3, v___x_3223_);
lean_ctor_set(v___x_3231_, 4, v___x_3230_);
v___x_3232_ = lean_st_mk_ref(v___x_3231_);
lean_inc(v_declName_3211_);
v___x_3244_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3211_, v___x_3217_, v___x_3227_, v___x_3232_, v___y_3214_, v___y_3215_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___f_3249_; lean_object* v___x_3250_; 
lean_dec_ref(v___x_3244_);
v___x_3245_ = lean_box(v_attrKind_3213_);
v___x_3246_ = lean_box(v_showInfo_3208_);
v___x_3247_ = lean_box(v_minIndexable_3209_);
v___x_3248_ = lean_box(v___x_3217_);
v___f_3249_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_3249_, 0, v_stx_3212_);
lean_closure_set(v___f_3249_, 1, v_ext_3207_);
lean_closure_set(v___f_3249_, 2, v_declName_3211_);
lean_closure_set(v___f_3249_, 3, v___x_3245_);
lean_closure_set(v___f_3249_, 4, v___x_3246_);
lean_closure_set(v___f_3249_, 5, v___x_3247_);
lean_closure_set(v___f_3249_, 6, v___x_3248_);
lean_closure_set(v___f_3249_, 7, v_attrName_3210_);
v___x_3250_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_3249_, v___x_3218_, v___x_3227_, v___x_3232_, v___y_3214_, v___y_3215_);
lean_dec_ref(v___x_3227_);
v___y_3234_ = v___x_3250_;
goto v___jp_3233_;
}
else
{
lean_dec_ref(v___x_3227_);
lean_dec(v_stx_3212_);
lean_dec(v_declName_3211_);
lean_dec(v_attrName_3210_);
lean_dec_ref(v_ext_3207_);
v___y_3234_ = v___x_3244_;
goto v___jp_3233_;
}
v___jp_3233_:
{
if (lean_obj_tag(v___y_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3243_; 
v_a_3235_ = lean_ctor_get(v___y_3234_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___y_3234_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3237_ = v___y_3234_;
v_isShared_3238_ = v_isSharedCheck_3243_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___y_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3243_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3239_; lean_object* v___x_3241_; 
v___x_3239_ = lean_st_ref_get(v___x_3232_);
lean_dec(v___x_3232_);
lean_dec(v___x_3239_);
if (v_isShared_3238_ == 0)
{
v___x_3241_ = v___x_3237_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3235_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
else
{
lean_dec(v___x_3232_);
return v___y_3234_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v___x_3251_, lean_object* v_ext_3252_, lean_object* v_showInfo_3253_, lean_object* v_minIndexable_3254_, lean_object* v_attrName_3255_, lean_object* v_declName_3256_, lean_object* v_stx_3257_, lean_object* v_attrKind_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
uint8_t v_showInfo_boxed_3262_; uint8_t v_minIndexable_boxed_3263_; uint8_t v_attrKind_boxed_3264_; lean_object* v_res_3265_; 
v_showInfo_boxed_3262_ = lean_unbox(v_showInfo_3253_);
v_minIndexable_boxed_3263_ = lean_unbox(v_minIndexable_3254_);
v_attrKind_boxed_3264_ = lean_unbox(v_attrKind_3258_);
v_res_3265_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v___x_3251_, v_ext_3252_, v_showInfo_boxed_3262_, v_minIndexable_boxed_3263_, v_attrName_3255_, v_declName_3256_, v_stx_3257_, v_attrKind_boxed_3264_, v___y_3259_, v___y_3260_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
return v_res_3265_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_3288_, uint8_t v_minIndexable_3289_, uint8_t v_showInfo_3290_, lean_object* v_ext_3291_, lean_object* v_ref_3292_){
_start:
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___f_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___f_3299_; lean_object* v___y_3301_; lean_object* v___y_3302_; lean_object* v___y_3345_; 
v___x_3294_ = lean_box(1);
v___x_3295_ = lean_box(v_showInfo_3290_);
lean_inc_n(v_attrName_3288_, 2);
lean_inc_ref(v_ext_3291_);
v___f_3296_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_3296_, 0, v___x_3294_);
lean_closure_set(v___f_3296_, 1, v_ext_3291_);
lean_closure_set(v___f_3296_, 2, v___x_3295_);
lean_closure_set(v___f_3296_, 3, v_attrName_3288_);
v___x_3297_ = lean_box(v_showInfo_3290_);
v___x_3298_ = lean_box(v_minIndexable_3289_);
v___f_3299_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_3299_, 0, v___x_3294_);
lean_closure_set(v___f_3299_, 1, v_ext_3291_);
lean_closure_set(v___f_3299_, 2, v___x_3297_);
lean_closure_set(v___f_3299_, 3, v___x_3298_);
lean_closure_set(v___f_3299_, 4, v_attrName_3288_);
if (v_minIndexable_3289_ == 0)
{
if (v_showInfo_3290_ == 0)
{
lean_inc(v_attrName_3288_);
v___y_3345_ = v_attrName_3288_;
goto v___jp_3344_;
}
else
{
lean_object* v___x_3373_; lean_object* v___x_3374_; 
v___x_3373_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_3288_);
v___x_3374_ = lean_name_append_after(v_attrName_3288_, v___x_3373_);
v___y_3345_ = v___x_3374_;
goto v___jp_3344_;
}
}
else
{
if (v_showInfo_3290_ == 0)
{
lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_3288_);
v___x_3376_ = lean_name_append_after(v_attrName_3288_, v___x_3375_);
v___y_3345_ = v___x_3376_;
goto v___jp_3344_;
}
else
{
lean_object* v___x_3377_; lean_object* v___x_3378_; 
v___x_3377_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_3288_);
v___x_3378_ = lean_name_append_after(v_attrName_3288_, v___x_3377_);
v___y_3345_ = v___x_3378_;
goto v___jp_3344_;
}
}
v___jp_3300_:
{
lean_object* v___x_3303_; uint8_t v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_3304_ = 1;
v___x_3305_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3288_, v___x_3304_);
v___x_3306_ = lean_string_append(v___x_3303_, v___x_3305_);
v___x_3307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_3308_ = lean_string_append(v___x_3306_, v___x_3307_);
v___x_3309_ = lean_string_append(v___x_3308_, v___x_3305_);
v___x_3310_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_3311_ = lean_string_append(v___x_3309_, v___x_3310_);
v___x_3312_ = lean_string_append(v___x_3311_, v___x_3305_);
v___x_3313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_3314_ = lean_string_append(v___x_3312_, v___x_3313_);
v___x_3315_ = lean_string_append(v___x_3314_, v___x_3305_);
v___x_3316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_3317_ = lean_string_append(v___x_3315_, v___x_3316_);
v___x_3318_ = lean_string_append(v___x_3317_, v___x_3305_);
v___x_3319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_3320_ = lean_string_append(v___x_3318_, v___x_3319_);
v___x_3321_ = lean_string_append(v___x_3320_, v___x_3305_);
v___x_3322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_3323_ = lean_string_append(v___x_3321_, v___x_3322_);
v___x_3324_ = lean_string_append(v___x_3323_, v___x_3305_);
v___x_3325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_3326_ = lean_string_append(v___x_3324_, v___x_3325_);
v___x_3327_ = lean_string_append(v___x_3326_, v___x_3305_);
v___x_3328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_3329_ = lean_string_append(v___x_3327_, v___x_3328_);
v___x_3330_ = lean_string_append(v___x_3329_, v___x_3305_);
v___x_3331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_3332_ = lean_string_append(v___x_3330_, v___x_3331_);
v___x_3333_ = lean_string_append(v___x_3332_, v___x_3305_);
v___x_3334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_3335_ = lean_string_append(v___x_3333_, v___x_3334_);
v___x_3336_ = lean_string_append(v___x_3335_, v___x_3305_);
lean_dec_ref(v___x_3305_);
v___x_3337_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_3338_ = lean_string_append(v___x_3336_, v___x_3337_);
v___x_3339_ = lean_string_append(v___y_3302_, v___x_3338_);
lean_dec_ref(v___x_3338_);
v___x_3340_ = 1;
v___x_3341_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3341_, 0, v_ref_3292_);
lean_ctor_set(v___x_3341_, 1, v___y_3301_);
lean_ctor_set(v___x_3341_, 2, v___x_3339_);
lean_ctor_set_uint8(v___x_3341_, sizeof(void*)*3, v___x_3340_);
v___x_3342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
lean_ctor_set(v___x_3342_, 1, v___f_3299_);
lean_ctor_set(v___x_3342_, 2, v___f_3296_);
v___x_3343_ = l_Lean_registerBuiltinAttribute(v___x_3342_);
return v___x_3343_;
}
v___jp_3344_:
{
if (v_minIndexable_3289_ == 0)
{
if (v_showInfo_3290_ == 0)
{
lean_object* v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_3347_ = 1;
lean_inc(v_attrName_3288_);
v___x_3348_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3288_, v___x_3347_);
v___x_3349_ = lean_string_append(v___x_3346_, v___x_3348_);
lean_dec_ref(v___x_3348_);
v___x_3350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_3351_ = lean_string_append(v___x_3349_, v___x_3350_);
v___y_3301_ = v___y_3345_;
v___y_3302_ = v___x_3351_;
goto v___jp_3300_;
}
else
{
lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v___x_3352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3288_);
v___x_3353_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3288_, v_showInfo_3290_);
v___x_3354_ = lean_string_append(v___x_3352_, v___x_3353_);
v___x_3355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_3356_ = lean_string_append(v___x_3354_, v___x_3355_);
v___x_3357_ = lean_string_append(v___x_3356_, v___x_3353_);
lean_dec_ref(v___x_3353_);
v___x_3358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_3359_ = lean_string_append(v___x_3357_, v___x_3358_);
v___y_3301_ = v___y_3345_;
v___y_3302_ = v___x_3359_;
goto v___jp_3300_;
}
}
else
{
if (v_showInfo_3290_ == 0)
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3288_);
v___x_3361_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3288_, v_minIndexable_3289_);
v___x_3362_ = lean_string_append(v___x_3360_, v___x_3361_);
lean_dec_ref(v___x_3361_);
v___x_3363_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_3364_ = lean_string_append(v___x_3362_, v___x_3363_);
v___y_3301_ = v___y_3345_;
v___y_3302_ = v___x_3364_;
goto v___jp_3300_;
}
else
{
lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3288_);
v___x_3366_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3288_, v_showInfo_3290_);
v___x_3367_ = lean_string_append(v___x_3365_, v___x_3366_);
v___x_3368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_3369_ = lean_string_append(v___x_3367_, v___x_3368_);
v___x_3370_ = lean_string_append(v___x_3369_, v___x_3366_);
lean_dec_ref(v___x_3366_);
v___x_3371_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_3372_ = lean_string_append(v___x_3370_, v___x_3371_);
v___y_3301_ = v___y_3345_;
v___y_3302_ = v___x_3372_;
goto v___jp_3300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_3379_, lean_object* v_minIndexable_3380_, lean_object* v_showInfo_3381_, lean_object* v_ext_3382_, lean_object* v_ref_3383_, lean_object* v_a_3384_){
_start:
{
uint8_t v_minIndexable_boxed_3385_; uint8_t v_showInfo_boxed_3386_; lean_object* v_res_3387_; 
v_minIndexable_boxed_3385_ = lean_unbox(v_minIndexable_3380_);
v_showInfo_boxed_3386_ = lean_unbox(v_showInfo_3381_);
v_res_3387_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3379_, v_minIndexable_boxed_3385_, v_showInfo_boxed_3386_, v_ext_3382_, v_ref_3383_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_3388_, lean_object* v_msg_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_3396_, lean_object* v_msg_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_3396_, v_msg_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_3404_, uint8_t v_attrKind_3405_, uint8_t v_showInfo_3406_, uint8_t v_minIndexable_3407_, lean_object* v_as_3408_, lean_object* v_as_x27_3409_, lean_object* v_b_3410_, lean_object* v_a_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3404_, v_attrKind_3405_, v_showInfo_3406_, v_minIndexable_3407_, v_as_x27_3409_, v_b_3410_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_3418_, lean_object* v_attrKind_3419_, lean_object* v_showInfo_3420_, lean_object* v_minIndexable_3421_, lean_object* v_as_3422_, lean_object* v_as_x27_3423_, lean_object* v_b_3424_, lean_object* v_a_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
uint8_t v_attrKind_boxed_3431_; uint8_t v_showInfo_boxed_3432_; uint8_t v_minIndexable_boxed_3433_; lean_object* v_res_3434_; 
v_attrKind_boxed_3431_ = lean_unbox(v_attrKind_3419_);
v_showInfo_boxed_3432_ = lean_unbox(v_showInfo_3420_);
v_minIndexable_boxed_3433_ = lean_unbox(v_minIndexable_3421_);
v_res_3434_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_3418_, v_attrKind_boxed_3431_, v_showInfo_boxed_3432_, v_minIndexable_boxed_3433_, v_as_3422_, v_as_x27_3423_, v_b_3424_, v_a_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3429_);
lean_dec_ref(v___y_3428_);
lean_dec(v___y_3427_);
lean_dec_ref(v___y_3426_);
lean_dec(v_as_x27_3423_);
lean_dec(v_as_3422_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object* v_00_u03b1_3435_, lean_object* v_x_3436_, uint8_t v_isExporting_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
lean_object* v___x_3443_; 
v___x_3443_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3436_, v_isExporting_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3444_, lean_object* v_x_3445_, lean_object* v_isExporting_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
uint8_t v_isExporting_boxed_3452_; lean_object* v_res_3453_; 
v_isExporting_boxed_3452_ = lean_unbox(v_isExporting_3446_);
v_res_3453_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(v_00_u03b1_3444_, v_x_3445_, v_isExporting_boxed_3452_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
lean_dec(v___y_3450_);
lean_dec_ref(v___y_3449_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_3454_, lean_object* v_x_3455_, uint8_t v_when_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v___x_3462_; 
v___x_3462_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3455_, v_when_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_3463_, lean_object* v_x_3464_, lean_object* v_when_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
uint8_t v_when_boxed_3471_; lean_object* v_res_3472_; 
v_when_boxed_3471_ = lean_unbox(v_when_3465_);
v_res_3472_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_3463_, v_x_3464_, v_when_boxed_3471_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
lean_dec(v___y_3469_);
lean_dec_ref(v___y_3468_);
lean_dec(v___y_3467_);
lean_dec_ref(v___y_3466_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object* v_00_u03b2_3473_, lean_object* v_m_3474_, lean_object* v_a_3475_){
_start:
{
lean_object* v___x_3476_; 
v___x_3476_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_3474_, v_a_3475_);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3477_, lean_object* v_m_3478_, lean_object* v_a_3479_){
_start:
{
lean_object* v_res_3480_; 
v_res_3480_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(v_00_u03b2_3477_, v_m_3478_, v_a_3479_);
lean_dec(v_a_3479_);
lean_dec_ref(v_m_3478_);
return v_res_3480_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3481_, lean_object* v_x_3482_, lean_object* v_x_3483_){
_start:
{
uint8_t v___x_3484_; 
v___x_3484_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_3482_, v_x_3483_);
return v___x_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3485_, lean_object* v_x_3486_, lean_object* v_x_3487_){
_start:
{
uint8_t v_res_3488_; lean_object* v_r_3489_; 
v_res_3488_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(v_00_u03b2_3485_, v_x_3486_, v_x_3487_);
lean_dec_ref(v_x_3487_);
lean_dec_ref(v_x_3486_);
v_r_3489_ = lean_box(v_res_3488_);
return v_r_3489_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_3490_, lean_object* v_a_3491_, lean_object* v_x_3492_){
_start:
{
lean_object* v___x_3493_; 
v___x_3493_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_3491_, v_x_3492_);
return v___x_3493_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3494_, lean_object* v_a_3495_, lean_object* v_x_3496_){
_start:
{
lean_object* v_res_3497_; 
v_res_3497_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(v_00_u03b2_3494_, v_a_3495_, v_x_3496_);
lean_dec(v_x_3496_);
lean_dec(v_a_3495_);
return v_res_3497_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3498_, lean_object* v_x_3499_, size_t v_x_3500_, lean_object* v_x_3501_){
_start:
{
uint8_t v___x_3502_; 
v___x_3502_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_3499_, v_x_3500_, v_x_3501_);
return v___x_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3503_, lean_object* v_x_3504_, lean_object* v_x_3505_, lean_object* v_x_3506_){
_start:
{
size_t v_x_17102__boxed_3507_; uint8_t v_res_3508_; lean_object* v_r_3509_; 
v_x_17102__boxed_3507_ = lean_unbox_usize(v_x_3505_);
lean_dec(v_x_3505_);
v_res_3508_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(v_00_u03b2_3503_, v_x_3504_, v_x_17102__boxed_3507_, v_x_3506_);
lean_dec_ref(v_x_3506_);
lean_dec_ref(v_x_3504_);
v_r_3509_ = lean_box(v_res_3508_);
return v_r_3509_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_3510_, lean_object* v_keys_3511_, lean_object* v_vals_3512_, lean_object* v_heq_3513_, lean_object* v_i_3514_, lean_object* v_k_3515_){
_start:
{
uint8_t v___x_3516_; 
v___x_3516_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_3511_, v_i_3514_, v_k_3515_);
return v___x_3516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3517_, lean_object* v_keys_3518_, lean_object* v_vals_3519_, lean_object* v_heq_3520_, lean_object* v_i_3521_, lean_object* v_k_3522_){
_start:
{
uint8_t v_res_3523_; lean_object* v_r_3524_; 
v_res_3523_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(v_00_u03b2_3517_, v_keys_3518_, v_vals_3519_, v_heq_3520_, v_i_3521_, v_k_3522_);
lean_dec_ref(v_k_3522_);
lean_dec_ref(v_vals_3519_);
lean_dec_ref(v_keys_3518_);
v_r_3524_ = lean_box(v_res_3523_);
return v_r_3524_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3525_ = lean_box(0);
v___x_3526_ = lean_unsigned_to_nat(16u);
v___x_3527_ = lean_mk_array(v___x_3526_, v___x_3525_);
return v___x_3527_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3528_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3529_ = lean_unsigned_to_nat(0u);
v___x_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3529_);
lean_ctor_set(v___x_3530_, 1, v___x_3528_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; 
v___x_3532_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3533_ = lean_st_mk_ref(v___x_3532_);
v___x_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3533_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_3535_){
_start:
{
lean_object* v_res_3536_; 
v_res_3536_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_3537_, lean_object* v_msg_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_ref_3542_; lean_object* v___x_3543_; lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3589_; 
v_ref_3542_ = lean_ctor_get(v___y_3539_, 5);
v___x_3543_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_3538_, v___y_3539_, v___y_3540_);
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3546_ = v___x_3543_;
v_isShared_3547_ = v_isSharedCheck_3589_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3543_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3589_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3548_; lean_object* v_traceState_3549_; lean_object* v_env_3550_; lean_object* v_nextMacroScope_3551_; lean_object* v_ngen_3552_; lean_object* v_auxDeclNGen_3553_; lean_object* v_cache_3554_; lean_object* v_messages_3555_; lean_object* v_infoState_3556_; lean_object* v_snapshotTasks_3557_; lean_object* v_newDecls_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3588_; 
v___x_3548_ = lean_st_ref_take(v___y_3540_);
v_traceState_3549_ = lean_ctor_get(v___x_3548_, 4);
v_env_3550_ = lean_ctor_get(v___x_3548_, 0);
v_nextMacroScope_3551_ = lean_ctor_get(v___x_3548_, 1);
v_ngen_3552_ = lean_ctor_get(v___x_3548_, 2);
v_auxDeclNGen_3553_ = lean_ctor_get(v___x_3548_, 3);
v_cache_3554_ = lean_ctor_get(v___x_3548_, 5);
v_messages_3555_ = lean_ctor_get(v___x_3548_, 6);
v_infoState_3556_ = lean_ctor_get(v___x_3548_, 7);
v_snapshotTasks_3557_ = lean_ctor_get(v___x_3548_, 8);
v_newDecls_3558_ = lean_ctor_get(v___x_3548_, 9);
v_isSharedCheck_3588_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3560_ = v___x_3548_;
v_isShared_3561_ = v_isSharedCheck_3588_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_newDecls_3558_);
lean_inc(v_snapshotTasks_3557_);
lean_inc(v_infoState_3556_);
lean_inc(v_messages_3555_);
lean_inc(v_cache_3554_);
lean_inc(v_traceState_3549_);
lean_inc(v_auxDeclNGen_3553_);
lean_inc(v_ngen_3552_);
lean_inc(v_nextMacroScope_3551_);
lean_inc(v_env_3550_);
lean_dec(v___x_3548_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3588_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
uint64_t v_tid_3562_; lean_object* v_traces_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3587_; 
v_tid_3562_ = lean_ctor_get_uint64(v_traceState_3549_, sizeof(void*)*1);
v_traces_3563_ = lean_ctor_get(v_traceState_3549_, 0);
v_isSharedCheck_3587_ = !lean_is_exclusive(v_traceState_3549_);
if (v_isSharedCheck_3587_ == 0)
{
v___x_3565_ = v_traceState_3549_;
v_isShared_3566_ = v_isSharedCheck_3587_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_traces_3563_);
lean_dec(v_traceState_3549_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3587_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3567_; double v___x_3568_; uint8_t v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3577_; 
v___x_3567_ = lean_box(0);
v___x_3568_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_3569_ = 0;
v___x_3570_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_3571_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3571_, 0, v_cls_3537_);
lean_ctor_set(v___x_3571_, 1, v___x_3567_);
lean_ctor_set(v___x_3571_, 2, v___x_3570_);
lean_ctor_set_float(v___x_3571_, sizeof(void*)*3, v___x_3568_);
lean_ctor_set_float(v___x_3571_, sizeof(void*)*3 + 8, v___x_3568_);
lean_ctor_set_uint8(v___x_3571_, sizeof(void*)*3 + 16, v___x_3569_);
v___x_3572_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_3573_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3571_);
lean_ctor_set(v___x_3573_, 1, v_a_3544_);
lean_ctor_set(v___x_3573_, 2, v___x_3572_);
lean_inc(v_ref_3542_);
v___x_3574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3574_, 0, v_ref_3542_);
lean_ctor_set(v___x_3574_, 1, v___x_3573_);
v___x_3575_ = l_Lean_PersistentArray_push___redArg(v_traces_3563_, v___x_3574_);
if (v_isShared_3566_ == 0)
{
lean_ctor_set(v___x_3565_, 0, v___x_3575_);
v___x_3577_ = v___x_3565_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3575_);
lean_ctor_set_uint64(v_reuseFailAlloc_3586_, sizeof(void*)*1, v_tid_3562_);
v___x_3577_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
lean_object* v___x_3579_; 
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 4, v___x_3577_);
v___x_3579_ = v___x_3560_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_env_3550_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_nextMacroScope_3551_);
lean_ctor_set(v_reuseFailAlloc_3585_, 2, v_ngen_3552_);
lean_ctor_set(v_reuseFailAlloc_3585_, 3, v_auxDeclNGen_3553_);
lean_ctor_set(v_reuseFailAlloc_3585_, 4, v___x_3577_);
lean_ctor_set(v_reuseFailAlloc_3585_, 5, v_cache_3554_);
lean_ctor_set(v_reuseFailAlloc_3585_, 6, v_messages_3555_);
lean_ctor_set(v_reuseFailAlloc_3585_, 7, v_infoState_3556_);
lean_ctor_set(v_reuseFailAlloc_3585_, 8, v_snapshotTasks_3557_);
lean_ctor_set(v_reuseFailAlloc_3585_, 9, v_newDecls_3558_);
v___x_3579_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3583_; 
v___x_3580_ = lean_st_ref_set(v___y_3540_, v___x_3579_);
v___x_3581_ = lean_box(0);
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 0, v___x_3581_);
v___x_3583_ = v___x_3546_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3581_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_3590_, lean_object* v_msg_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3590_, v_msg_3591_, v___y_3592_, v___y_3593_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_3596_, uint8_t v_isMeta_3597_, lean_object* v_hint_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___x_3602_; lean_object* v_env_3603_; uint8_t v_isExporting_3604_; lean_object* v___x_3605_; lean_object* v_env_3606_; lean_object* v___x_3607_; lean_object* v_entry_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___y_3613_; lean_object* v___x_3639_; uint8_t v___x_3640_; 
v___x_3602_ = lean_st_ref_get(v___y_3600_);
v_env_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc_ref(v_env_3603_);
lean_dec(v___x_3602_);
v_isExporting_3604_ = lean_ctor_get_uint8(v_env_3603_, sizeof(void*)*8);
lean_dec_ref(v_env_3603_);
v___x_3605_ = lean_st_ref_get(v___y_3600_);
v_env_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc_ref(v_env_3606_);
lean_dec(v___x_3605_);
v___x_3607_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_3596_);
v_entry_3608_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3608_, 0, v_mod_3596_);
lean_ctor_set_uint8(v_entry_3608_, sizeof(void*)*1, v_isExporting_3604_);
lean_ctor_set_uint8(v_entry_3608_, sizeof(void*)*1 + 1, v_isMeta_3597_);
v___x_3609_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3610_ = lean_box(1);
v___x_3611_ = lean_box(0);
v___x_3639_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3607_, v___x_3609_, v_env_3606_, v___x_3610_, v___x_3611_);
v___x_3640_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_3639_, v_entry_3608_);
lean_dec(v___x_3639_);
if (v___x_3640_ == 0)
{
lean_object* v_options_3641_; uint8_t v_hasTrace_3642_; 
v_options_3641_ = lean_ctor_get(v___y_3599_, 2);
v_hasTrace_3642_ = lean_ctor_get_uint8(v_options_3641_, sizeof(void*)*1);
if (v_hasTrace_3642_ == 0)
{
lean_dec(v_hint_3598_);
lean_dec(v_mod_3596_);
v___y_3613_ = v___y_3600_;
goto v___jp_3612_;
}
else
{
lean_object* v_inheritedTraceOptions_3643_; lean_object* v_cls_3644_; lean_object* v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___x_3664_; uint8_t v___x_3665_; 
v_inheritedTraceOptions_3643_ = lean_ctor_get(v___y_3599_, 13);
v_cls_3644_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_3664_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
v___x_3665_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3643_, v_options_3641_, v___x_3664_);
if (v___x_3665_ == 0)
{
lean_dec(v_hint_3598_);
lean_dec(v_mod_3596_);
v___y_3613_ = v___y_3600_;
goto v___jp_3612_;
}
else
{
lean_object* v___x_3666_; lean_object* v___y_3668_; 
v___x_3666_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
if (v_isExporting_3604_ == 0)
{
lean_object* v___x_3675_; 
v___x_3675_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19));
v___y_3668_ = v___x_3675_;
goto v___jp_3667_;
}
else
{
lean_object* v___x_3676_; 
v___x_3676_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20));
v___y_3668_ = v___x_3676_;
goto v___jp_3667_;
}
v___jp_3667_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
lean_inc_ref(v___y_3668_);
v___x_3669_ = l_Lean_stringToMessageData(v___y_3668_);
v___x_3670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3666_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
v___x_3671_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16);
v___x_3672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3670_);
lean_ctor_set(v___x_3672_, 1, v___x_3671_);
if (v_isMeta_3597_ == 0)
{
lean_object* v___x_3673_; 
v___x_3673_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_3651_ = v___x_3672_;
v___y_3652_ = v___x_3673_;
goto v___jp_3650_;
}
else
{
lean_object* v___x_3674_; 
v___x_3674_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_3651_ = v___x_3672_;
v___y_3652_ = v___x_3674_;
goto v___jp_3650_;
}
}
}
v___jp_3645_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___y_3646_);
lean_ctor_set(v___x_3648_, 1, v___y_3647_);
v___x_3649_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3644_, v___x_3648_, v___y_3599_, v___y_3600_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_dec_ref(v___x_3649_);
v___y_3613_ = v___y_3600_;
goto v___jp_3612_;
}
else
{
lean_dec_ref(v_entry_3608_);
return v___x_3649_;
}
}
v___jp_3650_:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; uint8_t v___x_3659_; 
lean_inc_ref(v___y_3652_);
v___x_3653_ = l_Lean_stringToMessageData(v___y_3652_);
v___x_3654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___y_3651_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
v___x_3655_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_3656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3654_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v___x_3657_ = l_Lean_MessageData_ofName(v_mod_3596_);
v___x_3658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3656_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
v___x_3659_ = l_Lean_Name_isAnonymous(v_hint_3598_);
if (v___x_3659_ == 0)
{
lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3660_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_3661_ = l_Lean_MessageData_ofName(v_hint_3598_);
v___x_3662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3660_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___y_3646_ = v___x_3658_;
v___y_3647_ = v___x_3662_;
goto v___jp_3645_;
}
else
{
lean_object* v___x_3663_; 
lean_dec(v_hint_3598_);
v___x_3663_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_3646_ = v___x_3658_;
v___y_3647_ = v___x_3663_;
goto v___jp_3645_;
}
}
}
}
else
{
lean_object* v___x_3677_; lean_object* v___x_3678_; 
lean_dec_ref(v_entry_3608_);
lean_dec(v_hint_3598_);
lean_dec(v_mod_3596_);
v___x_3677_ = lean_box(0);
v___x_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3677_);
return v___x_3678_;
}
v___jp_3612_:
{
lean_object* v___x_3614_; lean_object* v_toEnvExtension_3615_; lean_object* v_env_3616_; lean_object* v_nextMacroScope_3617_; lean_object* v_ngen_3618_; lean_object* v_auxDeclNGen_3619_; lean_object* v_traceState_3620_; lean_object* v_messages_3621_; lean_object* v_infoState_3622_; lean_object* v_snapshotTasks_3623_; lean_object* v_newDecls_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3637_; 
v___x_3614_ = lean_st_ref_take(v___y_3613_);
v_toEnvExtension_3615_ = lean_ctor_get(v___x_3609_, 0);
v_env_3616_ = lean_ctor_get(v___x_3614_, 0);
v_nextMacroScope_3617_ = lean_ctor_get(v___x_3614_, 1);
v_ngen_3618_ = lean_ctor_get(v___x_3614_, 2);
v_auxDeclNGen_3619_ = lean_ctor_get(v___x_3614_, 3);
v_traceState_3620_ = lean_ctor_get(v___x_3614_, 4);
v_messages_3621_ = lean_ctor_get(v___x_3614_, 6);
v_infoState_3622_ = lean_ctor_get(v___x_3614_, 7);
v_snapshotTasks_3623_ = lean_ctor_get(v___x_3614_, 8);
v_newDecls_3624_ = lean_ctor_get(v___x_3614_, 9);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3637_ == 0)
{
lean_object* v_unused_3638_; 
v_unused_3638_ = lean_ctor_get(v___x_3614_, 5);
lean_dec(v_unused_3638_);
v___x_3626_ = v___x_3614_;
v_isShared_3627_ = v_isSharedCheck_3637_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_newDecls_3624_);
lean_inc(v_snapshotTasks_3623_);
lean_inc(v_infoState_3622_);
lean_inc(v_messages_3621_);
lean_inc(v_traceState_3620_);
lean_inc(v_auxDeclNGen_3619_);
lean_inc(v_ngen_3618_);
lean_inc(v_nextMacroScope_3617_);
lean_inc(v_env_3616_);
lean_dec(v___x_3614_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3637_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v_asyncMode_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3632_; 
v_asyncMode_3628_ = lean_ctor_get(v_toEnvExtension_3615_, 2);
v___x_3629_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3609_, v_env_3616_, v_entry_3608_, v_asyncMode_3628_, v___x_3611_);
v___x_3630_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 5, v___x_3630_);
lean_ctor_set(v___x_3626_, 0, v___x_3629_);
v___x_3632_ = v___x_3626_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v___x_3629_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v_nextMacroScope_3617_);
lean_ctor_set(v_reuseFailAlloc_3636_, 2, v_ngen_3618_);
lean_ctor_set(v_reuseFailAlloc_3636_, 3, v_auxDeclNGen_3619_);
lean_ctor_set(v_reuseFailAlloc_3636_, 4, v_traceState_3620_);
lean_ctor_set(v_reuseFailAlloc_3636_, 5, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3636_, 6, v_messages_3621_);
lean_ctor_set(v_reuseFailAlloc_3636_, 7, v_infoState_3622_);
lean_ctor_set(v_reuseFailAlloc_3636_, 8, v_snapshotTasks_3623_);
lean_ctor_set(v_reuseFailAlloc_3636_, 9, v_newDecls_3624_);
v___x_3632_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3633_ = lean_st_ref_set(v___y_3613_, v___x_3632_);
v___x_3634_ = lean_box(0);
v___x_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
return v___x_3635_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_3679_, lean_object* v_isMeta_3680_, lean_object* v_hint_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
uint8_t v_isMeta_boxed_3685_; lean_object* v_res_3686_; 
v_isMeta_boxed_3685_ = lean_unbox(v_isMeta_3680_);
v_res_3686_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_3679_, v_isMeta_boxed_3685_, v_hint_3681_, v___y_3682_, v___y_3683_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
return v_res_3686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_3687_, lean_object* v_declName_3688_, lean_object* v_as_3689_, size_t v_sz_3690_, size_t v_i_3691_, lean_object* v_b_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_){
_start:
{
uint8_t v___x_3696_; 
v___x_3696_ = lean_usize_dec_lt(v_i_3691_, v_sz_3690_);
if (v___x_3696_ == 0)
{
lean_object* v___x_3697_; 
lean_dec(v_declName_3688_);
v___x_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3697_, 0, v_b_3692_);
return v___x_3697_;
}
else
{
lean_object* v___x_3698_; lean_object* v_modules_3699_; lean_object* v___x_3700_; lean_object* v_a_3701_; lean_object* v___x_3702_; lean_object* v_toImport_3703_; lean_object* v_module_3704_; uint8_t v___x_3705_; lean_object* v___x_3706_; 
v___x_3698_ = l_Lean_Environment_header(v___x_3687_);
v_modules_3699_ = lean_ctor_get(v___x_3698_, 3);
lean_inc_ref(v_modules_3699_);
lean_dec_ref(v___x_3698_);
v___x_3700_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3701_ = lean_array_uget_borrowed(v_as_3689_, v_i_3691_);
v___x_3702_ = lean_array_get(v___x_3700_, v_modules_3699_, v_a_3701_);
lean_dec_ref(v_modules_3699_);
v_toImport_3703_ = lean_ctor_get(v___x_3702_, 0);
lean_inc_ref(v_toImport_3703_);
lean_dec(v___x_3702_);
v_module_3704_ = lean_ctor_get(v_toImport_3703_, 0);
lean_inc(v_module_3704_);
lean_dec_ref(v_toImport_3703_);
v___x_3705_ = 0;
lean_inc(v_declName_3688_);
v___x_3706_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3704_, v___x_3705_, v_declName_3688_, v___y_3693_, v___y_3694_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v___x_3707_; size_t v___x_3708_; size_t v___x_3709_; 
lean_dec_ref(v___x_3706_);
v___x_3707_ = lean_box(0);
v___x_3708_ = ((size_t)1ULL);
v___x_3709_ = lean_usize_add(v_i_3691_, v___x_3708_);
v_i_3691_ = v___x_3709_;
v_b_3692_ = v___x_3707_;
goto _start;
}
else
{
lean_dec(v_declName_3688_);
return v___x_3706_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_3711_, lean_object* v_declName_3712_, lean_object* v_as_3713_, lean_object* v_sz_3714_, lean_object* v_i_3715_, lean_object* v_b_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
size_t v_sz_boxed_3720_; size_t v_i_boxed_3721_; lean_object* v_res_3722_; 
v_sz_boxed_3720_ = lean_unbox_usize(v_sz_3714_);
lean_dec(v_sz_3714_);
v_i_boxed_3721_ = lean_unbox_usize(v_i_3715_);
lean_dec(v_i_3715_);
v_res_3722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_3711_, v_declName_3712_, v_as_3713_, v_sz_boxed_3720_, v_i_boxed_3721_, v_b_3716_, v___y_3717_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec_ref(v_as_3713_);
lean_dec_ref(v___x_3711_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_3723_, uint8_t v_isMeta_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
lean_object* v___x_3728_; lean_object* v_env_3732_; lean_object* v___y_3734_; lean_object* v___x_3747_; 
v___x_3728_ = lean_st_ref_get(v___y_3726_);
v_env_3732_ = lean_ctor_get(v___x_3728_, 0);
lean_inc_ref(v_env_3732_);
lean_dec(v___x_3728_);
v___x_3747_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3732_, v_declName_3723_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_dec_ref(v_env_3732_);
lean_dec(v_declName_3723_);
goto v___jp_3729_;
}
else
{
lean_object* v_val_3748_; lean_object* v___x_3749_; lean_object* v_modules_3750_; lean_object* v___x_3751_; uint8_t v___x_3752_; 
v_val_3748_ = lean_ctor_get(v___x_3747_, 0);
lean_inc(v_val_3748_);
lean_dec_ref(v___x_3747_);
v___x_3749_ = l_Lean_Environment_header(v_env_3732_);
v_modules_3750_ = lean_ctor_get(v___x_3749_, 3);
lean_inc_ref(v_modules_3750_);
lean_dec_ref(v___x_3749_);
v___x_3751_ = lean_array_get_size(v_modules_3750_);
v___x_3752_ = lean_nat_dec_lt(v_val_3748_, v___x_3751_);
if (v___x_3752_ == 0)
{
lean_dec_ref(v_modules_3750_);
lean_dec(v_val_3748_);
lean_dec_ref(v_env_3732_);
lean_dec(v_declName_3723_);
goto v___jp_3729_;
}
else
{
lean_object* v___x_3753_; lean_object* v_env_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; uint8_t v___y_3758_; 
v___x_3753_ = lean_st_ref_get(v___y_3726_);
v_env_3754_ = lean_ctor_get(v___x_3753_, 0);
lean_inc_ref(v_env_3754_);
lean_dec(v___x_3753_);
v___x_3755_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3756_ = lean_array_fget(v_modules_3750_, v_val_3748_);
lean_dec(v_val_3748_);
lean_dec_ref(v_modules_3750_);
if (v_isMeta_3724_ == 0)
{
lean_dec_ref(v_env_3754_);
v___y_3758_ = v_isMeta_3724_;
goto v___jp_3757_;
}
else
{
uint8_t v___x_3769_; 
lean_inc(v_declName_3723_);
v___x_3769_ = l_Lean_isMarkedMeta(v_env_3754_, v_declName_3723_);
if (v___x_3769_ == 0)
{
v___y_3758_ = v_isMeta_3724_;
goto v___jp_3757_;
}
else
{
uint8_t v___x_3770_; 
v___x_3770_ = 0;
v___y_3758_ = v___x_3770_;
goto v___jp_3757_;
}
}
v___jp_3757_:
{
lean_object* v_toImport_3759_; lean_object* v_module_3760_; lean_object* v___x_3761_; 
v_toImport_3759_ = lean_ctor_get(v___x_3756_, 0);
lean_inc_ref(v_toImport_3759_);
lean_dec(v___x_3756_);
v_module_3760_ = lean_ctor_get(v_toImport_3759_, 0);
lean_inc(v_module_3760_);
lean_dec_ref(v_toImport_3759_);
lean_inc(v_declName_3723_);
v___x_3761_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3760_, v___y_3758_, v_declName_3723_, v___y_3725_, v___y_3726_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
lean_dec_ref(v___x_3761_);
v___x_3762_ = l_Lean_indirectModUseExt;
v___x_3763_ = lean_box(1);
v___x_3764_ = lean_box(0);
lean_inc_ref(v_env_3732_);
v___x_3765_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3755_, v___x_3762_, v_env_3732_, v___x_3763_, v___x_3764_);
v___x_3766_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3765_, v_declName_3723_);
lean_dec(v___x_3765_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v___x_3767_; 
v___x_3767_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_3734_ = v___x_3767_;
goto v___jp_3733_;
}
else
{
lean_object* v_val_3768_; 
v_val_3768_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_val_3768_);
lean_dec_ref(v___x_3766_);
v___y_3734_ = v_val_3768_;
goto v___jp_3733_;
}
}
else
{
lean_dec_ref(v_env_3732_);
lean_dec(v_declName_3723_);
return v___x_3761_;
}
}
}
}
v___jp_3729_:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = lean_box(0);
v___x_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
return v___x_3731_;
}
v___jp_3733_:
{
lean_object* v___x_3735_; size_t v_sz_3736_; size_t v___x_3737_; lean_object* v___x_3738_; 
v___x_3735_ = lean_box(0);
v_sz_3736_ = lean_array_size(v___y_3734_);
v___x_3737_ = ((size_t)0ULL);
v___x_3738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_3732_, v_declName_3723_, v___y_3734_, v_sz_3736_, v___x_3737_, v___x_3735_, v___y_3725_, v___y_3726_);
lean_dec_ref(v___y_3734_);
lean_dec_ref(v_env_3732_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3745_; 
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3745_ == 0)
{
lean_object* v_unused_3746_; 
v_unused_3746_ = lean_ctor_get(v___x_3738_, 0);
lean_dec(v_unused_3746_);
v___x_3740_ = v___x_3738_;
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
else
{
lean_dec(v___x_3738_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3745_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3743_; 
if (v_isShared_3741_ == 0)
{
lean_ctor_set(v___x_3740_, 0, v___x_3735_);
v___x_3743_ = v___x_3740_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3735_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
}
else
{
return v___x_3738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_3771_, lean_object* v_isMeta_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_){
_start:
{
uint8_t v_isMeta_boxed_3776_; lean_object* v_res_3777_; 
v_isMeta_boxed_3776_ = lean_unbox(v_isMeta_3772_);
v_res_3777_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_3771_, v_isMeta_boxed_3776_, v___y_3773_, v___y_3774_);
lean_dec(v___y_3774_);
lean_dec_ref(v___y_3773_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_){
_start:
{
lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3782_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3783_ = lean_st_ref_get(v___x_3782_);
v___x_3784_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3783_, v_attrName_3778_);
lean_dec(v___x_3783_);
if (lean_obj_tag(v___x_3784_) == 1)
{
lean_object* v_val_3785_; lean_object* v_ext_3786_; lean_object* v_name_3787_; uint8_t v___x_3788_; lean_object* v___x_3789_; 
v_val_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_val_3785_);
v_ext_3786_ = lean_ctor_get(v_val_3785_, 1);
lean_inc_ref(v_ext_3786_);
lean_dec(v_val_3785_);
v_name_3787_ = lean_ctor_get(v_ext_3786_, 1);
lean_inc(v_name_3787_);
lean_dec_ref(v_ext_3786_);
v___x_3788_ = 1;
v___x_3789_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_3787_, v___x_3788_, v_a_3779_, v_a_3780_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v___x_3791_; uint8_t v_isShared_3792_; uint8_t v_isSharedCheck_3796_; 
v_isSharedCheck_3796_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3796_ == 0)
{
lean_object* v_unused_3797_; 
v_unused_3797_ = lean_ctor_get(v___x_3789_, 0);
lean_dec(v_unused_3797_);
v___x_3791_ = v___x_3789_;
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
else
{
lean_dec(v___x_3789_);
v___x_3791_ = lean_box(0);
v_isShared_3792_ = v_isSharedCheck_3796_;
goto v_resetjp_3790_;
}
v_resetjp_3790_:
{
lean_object* v___x_3794_; 
if (v_isShared_3792_ == 0)
{
lean_ctor_set(v___x_3791_, 0, v___x_3784_);
v___x_3794_ = v___x_3791_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3784_);
v___x_3794_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
return v___x_3794_;
}
}
}
else
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3805_; 
lean_dec_ref(v___x_3784_);
v_a_3798_ = lean_ctor_get(v___x_3789_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3789_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3800_ = v___x_3789_;
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3789_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3805_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3803_; 
if (v_isShared_3801_ == 0)
{
v___x_3803_ = v___x_3800_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_a_3798_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
}
else
{
lean_object* v___x_3806_; 
v___x_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3784_);
return v___x_3806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_){
_start:
{
lean_object* v_res_3811_; 
v_res_3811_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_3807_, v_a_3808_, v_a_3809_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
lean_dec(v_attrName_3807_);
return v_res_3811_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_3813_, lean_object* v_x_3814_){
_start:
{
if (lean_obj_tag(v_x_3814_) == 0)
{
return v_x_3813_;
}
else
{
lean_object* v_key_3815_; lean_object* v_value_3816_; lean_object* v_tail_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3843_; 
v_key_3815_ = lean_ctor_get(v_x_3814_, 0);
v_value_3816_ = lean_ctor_get(v_x_3814_, 1);
v_tail_3817_ = lean_ctor_get(v_x_3814_, 2);
v_isSharedCheck_3843_ = !lean_is_exclusive(v_x_3814_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3819_ = v_x_3814_;
v_isShared_3820_ = v_isSharedCheck_3843_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_tail_3817_);
lean_inc(v_value_3816_);
lean_inc(v_key_3815_);
lean_dec(v_x_3814_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3843_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3821_; uint64_t v___y_3823_; 
v___x_3821_ = lean_array_get_size(v_x_3813_);
if (lean_obj_tag(v_key_3815_) == 0)
{
uint64_t v___x_3841_; 
v___x_3841_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_3823_ = v___x_3841_;
goto v___jp_3822_;
}
else
{
uint64_t v_hash_3842_; 
v_hash_3842_ = lean_ctor_get_uint64(v_key_3815_, sizeof(void*)*2);
v___y_3823_ = v_hash_3842_;
goto v___jp_3822_;
}
v___jp_3822_:
{
uint64_t v___x_3824_; uint64_t v___x_3825_; uint64_t v_fold_3826_; uint64_t v___x_3827_; uint64_t v___x_3828_; uint64_t v___x_3829_; size_t v___x_3830_; size_t v___x_3831_; size_t v___x_3832_; size_t v___x_3833_; size_t v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3837_; 
v___x_3824_ = 32ULL;
v___x_3825_ = lean_uint64_shift_right(v___y_3823_, v___x_3824_);
v_fold_3826_ = lean_uint64_xor(v___y_3823_, v___x_3825_);
v___x_3827_ = 16ULL;
v___x_3828_ = lean_uint64_shift_right(v_fold_3826_, v___x_3827_);
v___x_3829_ = lean_uint64_xor(v_fold_3826_, v___x_3828_);
v___x_3830_ = lean_uint64_to_usize(v___x_3829_);
v___x_3831_ = lean_usize_of_nat(v___x_3821_);
v___x_3832_ = ((size_t)1ULL);
v___x_3833_ = lean_usize_sub(v___x_3831_, v___x_3832_);
v___x_3834_ = lean_usize_land(v___x_3830_, v___x_3833_);
v___x_3835_ = lean_array_uget_borrowed(v_x_3813_, v___x_3834_);
lean_inc(v___x_3835_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set(v___x_3819_, 2, v___x_3835_);
v___x_3837_ = v___x_3819_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_key_3815_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v_value_3816_);
lean_ctor_set(v_reuseFailAlloc_3840_, 2, v___x_3835_);
v___x_3837_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
lean_object* v___x_3838_; 
v___x_3838_ = lean_array_uset(v_x_3813_, v___x_3834_, v___x_3837_);
v_x_3813_ = v___x_3838_;
v_x_3814_ = v_tail_3817_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3844_, lean_object* v_source_3845_, lean_object* v_target_3846_){
_start:
{
lean_object* v___x_3847_; uint8_t v___x_3848_; 
v___x_3847_ = lean_array_get_size(v_source_3845_);
v___x_3848_ = lean_nat_dec_lt(v_i_3844_, v___x_3847_);
if (v___x_3848_ == 0)
{
lean_dec_ref(v_source_3845_);
lean_dec(v_i_3844_);
return v_target_3846_;
}
else
{
lean_object* v_es_3849_; lean_object* v___x_3850_; lean_object* v_source_3851_; lean_object* v_target_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; 
v_es_3849_ = lean_array_fget(v_source_3845_, v_i_3844_);
v___x_3850_ = lean_box(0);
v_source_3851_ = lean_array_fset(v_source_3845_, v_i_3844_, v___x_3850_);
v_target_3852_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3846_, v_es_3849_);
v___x_3853_ = lean_unsigned_to_nat(1u);
v___x_3854_ = lean_nat_add(v_i_3844_, v___x_3853_);
lean_dec(v_i_3844_);
v_i_3844_ = v___x_3854_;
v_source_3845_ = v_source_3851_;
v_target_3846_ = v_target_3852_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_3856_){
_start:
{
lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v_nbuckets_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3857_ = lean_array_get_size(v_data_3856_);
v___x_3858_ = lean_unsigned_to_nat(2u);
v_nbuckets_3859_ = lean_nat_mul(v___x_3857_, v___x_3858_);
v___x_3860_ = lean_unsigned_to_nat(0u);
v___x_3861_ = lean_box(0);
v___x_3862_ = lean_mk_array(v_nbuckets_3859_, v___x_3861_);
v___x_3863_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_3860_, v_data_3856_, v___x_3862_);
return v___x_3863_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_3864_, lean_object* v_x_3865_){
_start:
{
if (lean_obj_tag(v_x_3865_) == 0)
{
uint8_t v___x_3866_; 
v___x_3866_ = 0;
return v___x_3866_;
}
else
{
lean_object* v_key_3867_; lean_object* v_tail_3868_; uint8_t v___x_3869_; 
v_key_3867_ = lean_ctor_get(v_x_3865_, 0);
v_tail_3868_ = lean_ctor_get(v_x_3865_, 2);
v___x_3869_ = lean_name_eq(v_key_3867_, v_a_3864_);
if (v___x_3869_ == 0)
{
v_x_3865_ = v_tail_3868_;
goto _start;
}
else
{
return v___x_3869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_3871_, lean_object* v_x_3872_){
_start:
{
uint8_t v_res_3873_; lean_object* v_r_3874_; 
v_res_3873_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3871_, v_x_3872_);
lean_dec(v_x_3872_);
lean_dec(v_a_3871_);
v_r_3874_ = lean_box(v_res_3873_);
return v_r_3874_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_3875_, lean_object* v_b_3876_, lean_object* v_x_3877_){
_start:
{
if (lean_obj_tag(v_x_3877_) == 0)
{
lean_dec(v_b_3876_);
lean_dec(v_a_3875_);
return v_x_3877_;
}
else
{
lean_object* v_key_3878_; lean_object* v_value_3879_; lean_object* v_tail_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3892_; 
v_key_3878_ = lean_ctor_get(v_x_3877_, 0);
v_value_3879_ = lean_ctor_get(v_x_3877_, 1);
v_tail_3880_ = lean_ctor_get(v_x_3877_, 2);
v_isSharedCheck_3892_ = !lean_is_exclusive(v_x_3877_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3882_ = v_x_3877_;
v_isShared_3883_ = v_isSharedCheck_3892_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_tail_3880_);
lean_inc(v_value_3879_);
lean_inc(v_key_3878_);
lean_dec(v_x_3877_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3892_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
uint8_t v___x_3884_; 
v___x_3884_ = lean_name_eq(v_key_3878_, v_a_3875_);
if (v___x_3884_ == 0)
{
lean_object* v___x_3885_; lean_object* v___x_3887_; 
v___x_3885_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3875_, v_b_3876_, v_tail_3880_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 2, v___x_3885_);
v___x_3887_ = v___x_3882_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v_key_3878_);
lean_ctor_set(v_reuseFailAlloc_3888_, 1, v_value_3879_);
lean_ctor_set(v_reuseFailAlloc_3888_, 2, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
else
{
lean_object* v___x_3890_; 
lean_dec(v_value_3879_);
lean_dec(v_key_3878_);
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 1, v_b_3876_);
lean_ctor_set(v___x_3882_, 0, v_a_3875_);
v___x_3890_ = v___x_3882_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3875_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_b_3876_);
lean_ctor_set(v_reuseFailAlloc_3891_, 2, v_tail_3880_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_3893_, lean_object* v_a_3894_, lean_object* v_b_3895_){
_start:
{
lean_object* v_size_3896_; lean_object* v_buckets_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3943_; 
v_size_3896_ = lean_ctor_get(v_m_3893_, 0);
v_buckets_3897_ = lean_ctor_get(v_m_3893_, 1);
v_isSharedCheck_3943_ = !lean_is_exclusive(v_m_3893_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3899_ = v_m_3893_;
v_isShared_3900_ = v_isSharedCheck_3943_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_buckets_3897_);
lean_inc(v_size_3896_);
lean_dec(v_m_3893_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3943_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3901_; uint64_t v___y_3903_; 
v___x_3901_ = lean_array_get_size(v_buckets_3897_);
if (lean_obj_tag(v_a_3894_) == 0)
{
uint64_t v___x_3941_; 
v___x_3941_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_3903_ = v___x_3941_;
goto v___jp_3902_;
}
else
{
uint64_t v_hash_3942_; 
v_hash_3942_ = lean_ctor_get_uint64(v_a_3894_, sizeof(void*)*2);
v___y_3903_ = v_hash_3942_;
goto v___jp_3902_;
}
v___jp_3902_:
{
uint64_t v___x_3904_; uint64_t v___x_3905_; uint64_t v_fold_3906_; uint64_t v___x_3907_; uint64_t v___x_3908_; uint64_t v___x_3909_; size_t v___x_3910_; size_t v___x_3911_; size_t v___x_3912_; size_t v___x_3913_; size_t v___x_3914_; lean_object* v_bkt_3915_; uint8_t v___x_3916_; 
v___x_3904_ = 32ULL;
v___x_3905_ = lean_uint64_shift_right(v___y_3903_, v___x_3904_);
v_fold_3906_ = lean_uint64_xor(v___y_3903_, v___x_3905_);
v___x_3907_ = 16ULL;
v___x_3908_ = lean_uint64_shift_right(v_fold_3906_, v___x_3907_);
v___x_3909_ = lean_uint64_xor(v_fold_3906_, v___x_3908_);
v___x_3910_ = lean_uint64_to_usize(v___x_3909_);
v___x_3911_ = lean_usize_of_nat(v___x_3901_);
v___x_3912_ = ((size_t)1ULL);
v___x_3913_ = lean_usize_sub(v___x_3911_, v___x_3912_);
v___x_3914_ = lean_usize_land(v___x_3910_, v___x_3913_);
v_bkt_3915_ = lean_array_uget_borrowed(v_buckets_3897_, v___x_3914_);
v___x_3916_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3894_, v_bkt_3915_);
if (v___x_3916_ == 0)
{
lean_object* v___x_3917_; lean_object* v_size_x27_3918_; lean_object* v___x_3919_; lean_object* v_buckets_x27_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; uint8_t v___x_3926_; 
v___x_3917_ = lean_unsigned_to_nat(1u);
v_size_x27_3918_ = lean_nat_add(v_size_3896_, v___x_3917_);
lean_dec(v_size_3896_);
lean_inc(v_bkt_3915_);
v___x_3919_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3919_, 0, v_a_3894_);
lean_ctor_set(v___x_3919_, 1, v_b_3895_);
lean_ctor_set(v___x_3919_, 2, v_bkt_3915_);
v_buckets_x27_3920_ = lean_array_uset(v_buckets_3897_, v___x_3914_, v___x_3919_);
v___x_3921_ = lean_unsigned_to_nat(4u);
v___x_3922_ = lean_nat_mul(v_size_x27_3918_, v___x_3921_);
v___x_3923_ = lean_unsigned_to_nat(3u);
v___x_3924_ = lean_nat_div(v___x_3922_, v___x_3923_);
lean_dec(v___x_3922_);
v___x_3925_ = lean_array_get_size(v_buckets_x27_3920_);
v___x_3926_ = lean_nat_dec_le(v___x_3924_, v___x_3925_);
lean_dec(v___x_3924_);
if (v___x_3926_ == 0)
{
lean_object* v_val_3927_; lean_object* v___x_3929_; 
v_val_3927_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_3920_);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 1, v_val_3927_);
lean_ctor_set(v___x_3899_, 0, v_size_x27_3918_);
v___x_3929_ = v___x_3899_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_size_x27_3918_);
lean_ctor_set(v_reuseFailAlloc_3930_, 1, v_val_3927_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
else
{
lean_object* v___x_3932_; 
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 1, v_buckets_x27_3920_);
lean_ctor_set(v___x_3899_, 0, v_size_x27_3918_);
v___x_3932_ = v___x_3899_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3933_; 
v_reuseFailAlloc_3933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_size_x27_3918_);
lean_ctor_set(v_reuseFailAlloc_3933_, 1, v_buckets_x27_3920_);
v___x_3932_ = v_reuseFailAlloc_3933_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
return v___x_3932_;
}
}
}
else
{
lean_object* v___x_3934_; lean_object* v_buckets_x27_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3939_; 
lean_inc(v_bkt_3915_);
v___x_3934_ = lean_box(0);
v_buckets_x27_3935_ = lean_array_uset(v_buckets_3897_, v___x_3914_, v___x_3934_);
v___x_3936_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3894_, v_b_3895_, v_bkt_3915_);
v___x_3937_ = lean_array_uset(v_buckets_x27_3935_, v___x_3914_, v___x_3936_);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 1, v___x_3937_);
v___x_3939_ = v___x_3899_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_size_3896_);
lean_ctor_set(v_reuseFailAlloc_3940_, 1, v___x_3937_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_3944_, lean_object* v_ref_3945_){
_start:
{
lean_object* v___x_3947_; 
lean_inc(v_ref_3945_);
v___x_3947_ = l_Lean_Meta_Grind_mkExtension(v_ref_3945_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; uint8_t v___x_3949_; uint8_t v___x_3950_; lean_object* v___x_3951_; 
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc_n(v_a_3948_, 2);
lean_dec_ref(v___x_3947_);
v___x_3949_ = 0;
v___x_3950_ = 1;
lean_inc(v_ref_3945_);
lean_inc(v_attrName_3944_);
v___x_3951_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3944_, v___x_3949_, v___x_3950_, v_a_3948_, v_ref_3945_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v___x_3952_; 
lean_dec_ref(v___x_3951_);
lean_inc(v_ref_3945_);
lean_inc(v_a_3948_);
lean_inc(v_attrName_3944_);
v___x_3952_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3944_, v___x_3949_, v___x_3949_, v_a_3948_, v_ref_3945_);
if (lean_obj_tag(v___x_3952_) == 0)
{
lean_object* v___x_3953_; 
lean_dec_ref(v___x_3952_);
lean_inc(v_ref_3945_);
lean_inc(v_a_3948_);
lean_inc(v_attrName_3944_);
v___x_3953_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3944_, v___x_3950_, v___x_3950_, v_a_3948_, v_ref_3945_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v___x_3954_; 
lean_dec_ref(v___x_3953_);
lean_inc(v_a_3948_);
lean_inc(v_attrName_3944_);
v___x_3954_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3944_, v___x_3950_, v___x_3949_, v_a_3948_, v_ref_3945_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3965_; 
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3965_ == 0)
{
lean_object* v_unused_3966_; 
v_unused_3966_ = lean_ctor_get(v___x_3954_, 0);
lean_dec(v_unused_3966_);
v___x_3956_ = v___x_3954_;
v_isShared_3957_ = v_isSharedCheck_3965_;
goto v_resetjp_3955_;
}
else
{
lean_dec(v___x_3954_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3965_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3963_; 
v___x_3958_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3959_ = lean_st_ref_take(v___x_3958_);
lean_inc(v_a_3948_);
v___x_3960_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_3959_, v_attrName_3944_, v_a_3948_);
v___x_3961_ = lean_st_ref_set(v___x_3958_, v___x_3960_);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 0, v_a_3948_);
v___x_3963_ = v___x_3956_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3948_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
else
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3974_; 
lean_dec(v_a_3948_);
lean_dec(v_attrName_3944_);
v_a_3967_ = lean_ctor_get(v___x_3954_, 0);
v_isSharedCheck_3974_ = !lean_is_exclusive(v___x_3954_);
if (v_isSharedCheck_3974_ == 0)
{
v___x_3969_ = v___x_3954_;
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3954_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3974_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v___x_3972_; 
if (v_isShared_3970_ == 0)
{
v___x_3972_ = v___x_3969_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v_a_3967_);
v___x_3972_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
return v___x_3972_;
}
}
}
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec(v_a_3948_);
lean_dec(v_ref_3945_);
lean_dec(v_attrName_3944_);
v_a_3975_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3953_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3953_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3975_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
else
{
lean_object* v_a_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_3990_; 
lean_dec(v_a_3948_);
lean_dec(v_ref_3945_);
lean_dec(v_attrName_3944_);
v_a_3983_ = lean_ctor_get(v___x_3952_, 0);
v_isSharedCheck_3990_ = !lean_is_exclusive(v___x_3952_);
if (v_isSharedCheck_3990_ == 0)
{
v___x_3985_ = v___x_3952_;
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
else
{
lean_inc(v_a_3983_);
lean_dec(v___x_3952_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_3990_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3988_; 
if (v_isShared_3986_ == 0)
{
v___x_3988_ = v___x_3985_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v_a_3983_);
v___x_3988_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
return v___x_3988_;
}
}
}
}
else
{
lean_object* v_a_3991_; lean_object* v___x_3993_; uint8_t v_isShared_3994_; uint8_t v_isSharedCheck_3998_; 
lean_dec(v_a_3948_);
lean_dec(v_ref_3945_);
lean_dec(v_attrName_3944_);
v_a_3991_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3993_ = v___x_3951_;
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
else
{
lean_inc(v_a_3991_);
lean_dec(v___x_3951_);
v___x_3993_ = lean_box(0);
v_isShared_3994_ = v_isSharedCheck_3998_;
goto v_resetjp_3992_;
}
v_resetjp_3992_:
{
lean_object* v___x_3996_; 
if (v_isShared_3994_ == 0)
{
v___x_3996_ = v___x_3993_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v_a_3991_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
else
{
lean_dec(v_ref_3945_);
lean_dec(v_attrName_3944_);
return v___x_3947_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_3999_, lean_object* v_ref_4000_, lean_object* v_a_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Lean_Meta_Grind_registerAttr(v_attrName_3999_, v_ref_4000_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_4003_, lean_object* v_m_4004_, lean_object* v_a_4005_, lean_object* v_b_4006_){
_start:
{
lean_object* v___x_4007_; 
v___x_4007_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_4004_, v_a_4005_, v_b_4006_);
return v___x_4007_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_4008_, lean_object* v_a_4009_, lean_object* v_x_4010_){
_start:
{
uint8_t v___x_4011_; 
v___x_4011_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4009_, v_x_4010_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4012_, lean_object* v_a_4013_, lean_object* v_x_4014_){
_start:
{
uint8_t v_res_4015_; lean_object* v_r_4016_; 
v_res_4015_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_4012_, v_a_4013_, v_x_4014_);
lean_dec(v_x_4014_);
lean_dec(v_a_4013_);
v_r_4016_ = lean_box(v_res_4015_);
return v_r_4016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_4017_, lean_object* v_data_4018_){
_start:
{
lean_object* v___x_4019_; 
v___x_4019_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_4018_);
return v___x_4019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_4020_, lean_object* v_a_4021_, lean_object* v_b_4022_, lean_object* v_x_4023_){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4021_, v_b_4022_, v_x_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4025_, lean_object* v_i_4026_, lean_object* v_source_4027_, lean_object* v_target_4028_){
_start:
{
lean_object* v___x_4029_; 
v___x_4029_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_4026_, v_source_4027_, v_target_4028_);
return v___x_4029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4030_, lean_object* v_x_4031_, lean_object* v_x_4032_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_4031_, v_x_4032_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4040_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_4041_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_4042_ = l_Lean_Meta_Grind_registerAttr(v___x_4040_, v___x_4041_);
return v___x_4042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_4045_, lean_object* v_a_4046_){
_start:
{
lean_object* v___x_4048_; lean_object* v_env_4049_; lean_object* v___x_4050_; lean_object* v_ext_4051_; lean_object* v_toEnvExtension_4052_; lean_object* v_asyncMode_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v_casesTypes_4056_; uint8_t v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4048_ = lean_st_ref_get(v_a_4046_);
v_env_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc_ref(v_env_4049_);
lean_dec(v___x_4048_);
v___x_4050_ = l_Lean_Meta_Grind_grindExt;
v_ext_4051_ = lean_ctor_get(v___x_4050_, 1);
v_toEnvExtension_4052_ = lean_ctor_get(v_ext_4051_, 0);
v_asyncMode_4053_ = lean_ctor_get(v_toEnvExtension_4052_, 2);
v___x_4054_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4055_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4054_, v___x_4050_, v_env_4049_, v_asyncMode_4053_);
v_casesTypes_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc_ref(v_casesTypes_4056_);
lean_dec(v___x_4055_);
v___x_4057_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_4056_, v_declName_4045_);
lean_dec_ref(v_casesTypes_4056_);
v___x_4058_ = lean_box(v___x_4057_);
v___x_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
return v___x_4059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4060_, v_a_4061_);
lean_dec(v_a_4061_);
lean_dec(v_declName_4060_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_4064_, lean_object* v_a_4065_, lean_object* v_a_4066_){
_start:
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4064_, v_a_4066_);
return v___x_4068_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_){
_start:
{
lean_object* v_res_4073_; 
v_res_4073_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_4069_, v_a_4070_, v_a_4071_);
lean_dec(v_a_4071_);
lean_dec_ref(v_a_4070_);
lean_dec(v_declName_4069_);
return v_res_4073_;
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
