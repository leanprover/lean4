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
size_t lean_usize_sub(size_t, size_t);
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
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(12, 161, 226, 116, 111, 153, 146, 212)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "liaExt"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(148, 224, 62, 90, 13, 174, 224, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_liaExt;
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
lean_dec_ref_known(v_t_28_, 1);
v___x_31_ = lean_apply_1(v_k_29_, v_k_30_);
return v___x_31_;
}
case 1:
{
uint8_t v_eager_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_eager_32_ = lean_ctor_get_uint8(v_t_28_, 0);
lean_dec_ref_known(v_t_28_, 0);
v___x_33_ = lean_box(v_eager_32_);
v___x_34_ = lean_apply_1(v_k_29_, v___x_33_);
return v___x_34_;
}
case 5:
{
lean_object* v_prio_35_; lean_object* v___x_36_; 
v_prio_35_ = lean_ctor_get(v_t_28_, 0);
lean_inc(v_prio_35_);
lean_dec_ref_known(v_t_28_, 1);
v___x_36_ = lean_apply_1(v_k_29_, v_prio_35_);
return v___x_36_;
}
case 8:
{
uint8_t v_post_37_; uint8_t v_inv_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v_post_37_ = lean_ctor_get_uint8(v_t_28_, 0);
v_inv_38_ = lean_ctor_get_uint8(v_t_28_, 1);
lean_dec_ref_known(v_t_28_, 0);
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
lean_dec_ref_known(v___x_212_, 14);
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
lean_dec_ref_known(v___x_814_, 1);
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
lean_dec_ref_known(v___x_958_, 1);
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
v___x_1400_ = lean_nat_add(v___y_1397_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec(v___y_1397_);
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
lean_ctor_set(v___x_1404_, 3, v___y_1398_);
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
lean_ctor_set(v_reuseFailAlloc_1408_, 3, v___y_1398_);
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
v___y_1397_ = v___x_1422_;
v___y_1398_ = v___x_1421_;
v___y_1399_ = v_size_1423_;
goto v___jp_1396_;
}
else
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_unsigned_to_nat(0u);
v___y_1397_ = v___x_1422_;
v___y_1398_ = v___x_1421_;
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
v___x_1558_ = lean_nat_add(v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec(v___y_1556_);
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
lean_ctor_set(v___x_1538_, 3, v___y_1555_);
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
lean_ctor_set(v_reuseFailAlloc_1563_, 3, v___y_1555_);
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
v___y_1555_ = v___x_1570_;
v___y_1556_ = v___x_1571_;
v___y_1557_ = v_size_1572_;
goto v___jp_1554_;
}
else
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_unsigned_to_nat(0u);
v___y_1555_ = v___x_1570_;
v___y_1556_ = v___x_1571_;
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
lean_dec_ref_known(v___x_1731_, 1);
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(lean_object* v_x_1947_, size_t v_x_1948_, lean_object* v_x_1949_){
_start:
{
if (lean_obj_tag(v_x_1947_) == 0)
{
lean_object* v_es_1950_; lean_object* v___x_1951_; size_t v___x_1952_; size_t v___x_1953_; lean_object* v_j_1954_; lean_object* v___x_1955_; 
v_es_1950_ = lean_ctor_get(v_x_1947_, 0);
v___x_1951_ = lean_box(2);
v___x_1952_ = ((size_t)31ULL);
v___x_1953_ = lean_usize_land(v_x_1948_, v___x_1952_);
v_j_1954_ = lean_usize_to_nat(v___x_1953_);
v___x_1955_ = lean_array_get_borrowed(v___x_1951_, v_es_1950_, v_j_1954_);
lean_dec(v_j_1954_);
switch(lean_obj_tag(v___x_1955_))
{
case 0:
{
lean_object* v_key_1956_; uint8_t v___x_1957_; 
v_key_1956_ = lean_ctor_get(v___x_1955_, 0);
v___x_1957_ = lean_name_eq(v_x_1949_, v_key_1956_);
return v___x_1957_;
}
case 1:
{
lean_object* v_node_1958_; size_t v___x_1959_; size_t v___x_1960_; 
v_node_1958_ = lean_ctor_get(v___x_1955_, 0);
v___x_1959_ = ((size_t)5ULL);
v___x_1960_ = lean_usize_shift_right(v_x_1948_, v___x_1959_);
v_x_1947_ = v_node_1958_;
v_x_1948_ = v___x_1960_;
goto _start;
}
default: 
{
uint8_t v___x_1962_; 
v___x_1962_ = 0;
return v___x_1962_;
}
}
}
else
{
lean_object* v_ks_1963_; lean_object* v___x_1964_; uint8_t v___x_1965_; 
v_ks_1963_ = lean_ctor_get(v_x_1947_, 0);
v___x_1964_ = lean_unsigned_to_nat(0u);
v___x_1965_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_1963_, v___x_1964_, v_x_1949_);
return v___x_1965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_1966_, lean_object* v_x_1967_, lean_object* v_x_1968_){
_start:
{
size_t v_x_327__boxed_1969_; uint8_t v_res_1970_; lean_object* v_r_1971_; 
v_x_327__boxed_1969_ = lean_unbox_usize(v_x_1967_);
lean_dec(v_x_1967_);
v_res_1970_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_1966_, v_x_327__boxed_1969_, v_x_1968_);
lean_dec(v_x_1968_);
lean_dec_ref(v_x_1966_);
v_r_1971_ = lean_box(v_res_1970_);
return v_r_1971_;
}
}
static uint64_t _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1972_; uint64_t v___x_1973_; 
v___x_1972_ = lean_unsigned_to_nat(1723u);
v___x_1973_ = lean_uint64_of_nat(v___x_1972_);
return v___x_1973_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(lean_object* v_x_1974_, lean_object* v_x_1975_){
_start:
{
uint64_t v___y_1977_; 
if (lean_obj_tag(v_x_1975_) == 0)
{
uint64_t v___x_1980_; 
v___x_1980_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_1977_ = v___x_1980_;
goto v___jp_1976_;
}
else
{
uint64_t v_hash_1981_; 
v_hash_1981_ = lean_ctor_get_uint64(v_x_1975_, sizeof(void*)*2);
v___y_1977_ = v_hash_1981_;
goto v___jp_1976_;
}
v___jp_1976_:
{
size_t v___x_1978_; uint8_t v___x_1979_; 
v___x_1978_ = lean_uint64_to_usize(v___y_1977_);
v___x_1979_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_1974_, v___x_1978_, v_x_1975_);
return v___x_1979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___boxed(lean_object* v_x_1982_, lean_object* v_x_1983_){
_start:
{
uint8_t v_res_1984_; lean_object* v_r_1985_; 
v_res_1984_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_1982_, v_x_1983_);
lean_dec(v_x_1983_);
lean_dec_ref(v_x_1982_);
v_r_1985_ = lean_box(v_res_1984_);
return v_r_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(lean_object* v_ext_1986_, lean_object* v_declName_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v___x_1990_; lean_object* v_ext_1991_; lean_object* v_toEnvExtension_1992_; lean_object* v_env_1993_; lean_object* v_asyncMode_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v_extThms_1997_; uint8_t v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1990_ = lean_st_ref_get(v_a_1988_);
v_ext_1991_ = lean_ctor_get(v_ext_1986_, 1);
v_toEnvExtension_1992_ = lean_ctor_get(v_ext_1991_, 0);
v_env_1993_ = lean_ctor_get(v___x_1990_, 0);
lean_inc_ref(v_env_1993_);
lean_dec(v___x_1990_);
v_asyncMode_1994_ = lean_ctor_get(v_toEnvExtension_1992_, 2);
v___x_1995_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1996_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1995_, v_ext_1986_, v_env_1993_, v_asyncMode_1994_);
v_extThms_1997_ = lean_ctor_get(v___x_1996_, 1);
lean_inc_ref(v_extThms_1997_);
lean_dec(v___x_1996_);
v___x_1998_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_extThms_1997_, v_declName_1987_);
lean_dec_ref(v_extThms_1997_);
v___x_1999_ = lean_box(v___x_1998_);
v___x_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg___boxed(lean_object* v_ext_2001_, lean_object* v_declName_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2001_, v_declName_2002_, v_a_2003_);
lean_dec(v_a_2003_);
lean_dec(v_declName_2002_);
lean_dec_ref(v_ext_2001_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(lean_object* v_ext_2006_, lean_object* v_declName_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2006_, v_declName_2007_, v_a_2009_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___boxed(lean_object* v_ext_2012_, lean_object* v_declName_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem(v_ext_2012_, v_declName_2013_, v_a_2014_, v_a_2015_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_declName_2013_);
lean_dec_ref(v_ext_2012_);
return v_res_2017_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(lean_object* v_00_u03b2_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_){
_start:
{
uint8_t v___x_2021_; 
v___x_2021_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg(v_x_2019_, v_x_2020_);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___boxed(lean_object* v_00_u03b2_2022_, lean_object* v_x_2023_, lean_object* v_x_2024_){
_start:
{
uint8_t v_res_2025_; lean_object* v_r_2026_; 
v_res_2025_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0(v_00_u03b2_2022_, v_x_2023_, v_x_2024_);
lean_dec(v_x_2024_);
lean_dec_ref(v_x_2023_);
v_r_2026_ = lean_box(v_res_2025_);
return v_r_2026_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(lean_object* v_00_u03b2_2027_, lean_object* v_x_2028_, size_t v_x_2029_, lean_object* v_x_2030_){
_start:
{
uint8_t v___x_2031_; 
v___x_2031_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_2028_, v_x_2029_, v_x_2030_);
return v___x_2031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2032_, lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
size_t v_x_418__boxed_2036_; uint8_t v_res_2037_; lean_object* v_r_2038_; 
v_x_418__boxed_2036_ = lean_unbox_usize(v_x_2034_);
lean_dec(v_x_2034_);
v_res_2037_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_2032_, v_x_2033_, v_x_418__boxed_2036_, v_x_2035_);
lean_dec(v_x_2035_);
lean_dec_ref(v_x_2033_);
v_r_2038_ = lean_box(v_res_2037_);
return v_r_2038_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2039_, lean_object* v_keys_2040_, lean_object* v_vals_2041_, lean_object* v_heq_2042_, lean_object* v_i_2043_, lean_object* v_k_2044_){
_start:
{
uint8_t v___x_2045_; 
v___x_2045_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_keys_2040_, v_i_2043_, v_k_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2046_, lean_object* v_keys_2047_, lean_object* v_vals_2048_, lean_object* v_heq_2049_, lean_object* v_i_2050_, lean_object* v_k_2051_){
_start:
{
uint8_t v_res_2052_; lean_object* v_r_2053_; 
v_res_2052_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1(v_00_u03b2_2046_, v_keys_2047_, v_vals_2048_, v_heq_2049_, v_i_2050_, v_k_2051_);
lean_dec(v_k_2051_);
lean_dec_ref(v_vals_2048_);
lean_dec_ref(v_keys_2047_);
v_r_2053_ = lean_box(v_res_2052_);
return v_r_2053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(lean_object* v_ext_2054_, lean_object* v_declName_2055_, lean_object* v_a_2056_){
_start:
{
lean_object* v___x_2058_; lean_object* v_ext_2059_; lean_object* v_toEnvExtension_2060_; lean_object* v_env_2061_; lean_object* v_asyncMode_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v_inj_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2058_ = lean_st_ref_get(v_a_2056_);
v_ext_2059_ = lean_ctor_get(v_ext_2054_, 1);
v_toEnvExtension_2060_ = lean_ctor_get(v_ext_2059_, 0);
v_env_2061_ = lean_ctor_get(v___x_2058_, 0);
lean_inc_ref(v_env_2061_);
lean_dec(v___x_2058_);
v_asyncMode_2062_ = lean_ctor_get(v_toEnvExtension_2060_, 2);
v___x_2063_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2064_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2063_, v_ext_2054_, v_env_2061_, v_asyncMode_2062_);
v_inj_2065_ = lean_ctor_get(v___x_2064_, 4);
lean_inc_ref(v_inj_2065_);
lean_dec(v___x_2064_);
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v_declName_2055_);
v___x_2067_ = l_Lean_Meta_Grind_Theorems_contains___redArg(v_inj_2065_, v___x_2066_);
lean_dec_ref_known(v___x_2066_, 1);
lean_dec_ref(v_inj_2065_);
v___x_2068_ = lean_box(v___x_2067_);
v___x_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg___boxed(lean_object* v_ext_2070_, lean_object* v_declName_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2070_, v_declName_2071_, v_a_2072_);
lean_dec(v_a_2072_);
lean_dec_ref(v_ext_2070_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(lean_object* v_ext_2075_, lean_object* v_declName_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2075_, v_declName_2076_, v_a_2078_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___boxed(lean_object* v_ext_2081_, lean_object* v_declName_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem(v_ext_2081_, v_declName_2082_, v_a_2083_, v_a_2084_);
lean_dec(v_a_2084_);
lean_dec_ref(v_a_2083_);
lean_dec_ref(v_ext_2081_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(lean_object* v_ext_2087_, lean_object* v_declName_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v___x_2091_; lean_object* v_ext_2092_; lean_object* v_toEnvExtension_2093_; lean_object* v_env_2094_; lean_object* v_asyncMode_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v_funCC_2098_; uint8_t v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2091_ = lean_st_ref_get(v_a_2089_);
v_ext_2092_ = lean_ctor_get(v_ext_2087_, 1);
v_toEnvExtension_2093_ = lean_ctor_get(v_ext_2092_, 0);
v_env_2094_ = lean_ctor_get(v___x_2091_, 0);
lean_inc_ref(v_env_2094_);
lean_dec(v___x_2091_);
v_asyncMode_2095_ = lean_ctor_get(v_toEnvExtension_2093_, 2);
v___x_2096_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_2097_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_2096_, v_ext_2087_, v_env_2094_, v_asyncMode_2095_);
v_funCC_2098_ = lean_ctor_get(v___x_2097_, 2);
lean_inc(v_funCC_2098_);
lean_dec(v___x_2097_);
v___x_2099_ = l_Lean_NameSet_contains(v_funCC_2098_, v_declName_2088_);
lean_dec(v_funCC_2098_);
v___x_2100_ = lean_box(v___x_2099_);
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg___boxed(lean_object* v_ext_2102_, lean_object* v_declName_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2102_, v_declName_2103_, v_a_2104_);
lean_dec(v_a_2104_);
lean_dec(v_declName_2103_);
lean_dec_ref(v_ext_2102_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(lean_object* v_ext_2107_, lean_object* v_declName_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2107_, v_declName_2108_, v_a_2110_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___boxed(lean_object* v_ext_2113_, lean_object* v_declName_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr(v_ext_2113_, v_declName_2114_, v_a_2115_, v_a_2116_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_declName_2114_);
lean_dec_ref(v_ext_2113_);
return v_res_2118_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2142_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__7));
v___x_2143_ = l_Lean_mkAtom(v___x_2142_);
return v___x_2143_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2144_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__9);
v___x_2145_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2146_ = lean_array_push(v___x_2145_, v___x_2144_);
return v___x_2146_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2155_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__14));
v___x_2156_ = l_Lean_mkAtom(v___x_2155_);
return v___x_2156_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__15);
v___x_2158_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2159_ = lean_array_push(v___x_2158_, v___x_2157_);
return v___x_2159_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2160_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__16);
v___x_2161_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13));
v___x_2162_ = lean_box(2);
v___x_2163_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
lean_ctor_set(v___x_2163_, 1, v___x_2161_);
lean_ctor_set(v___x_2163_, 2, v___x_2160_);
return v___x_2163_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__17);
v___x_2165_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__10);
v___x_2166_ = lean_array_push(v___x_2165_, v___x_2164_);
return v___x_2166_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19(void){
_start:
{
lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2167_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__18);
v___x_2168_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8));
v___x_2169_ = lean_box(2);
v___x_2170_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
lean_ctor_set(v___x_2170_, 1, v___x_2168_);
lean_ctor_set(v___x_2170_, 2, v___x_2167_);
return v___x_2170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20(void){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__19);
v___x_2172_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2173_ = lean_array_push(v___x_2172_, v___x_2171_);
return v___x_2173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21(void){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2174_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__20);
v___x_2175_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__6));
v___x_2176_ = lean_box(2);
v___x_2177_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
lean_ctor_set(v___x_2177_, 1, v___x_2175_);
lean_ctor_set(v___x_2177_, 2, v___x_2174_);
return v___x_2177_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__21);
v___x_2179_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2180_ = lean_array_push(v___x_2179_, v___x_2178_);
return v___x_2180_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v___x_2181_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__22);
v___x_2182_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4));
v___x_2183_ = lean_box(2);
v___x_2184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
lean_ctor_set(v___x_2184_, 1, v___x_2182_);
lean_ctor_set(v___x_2184_, 2, v___x_2181_);
return v___x_2184_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__23);
v___x_2186_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2));
v___x_2187_ = lean_array_push(v___x_2186_, v___x_2185_);
return v___x_2187_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25(void){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2188_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__24);
v___x_2189_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1));
v___x_2190_ = lean_box(2);
v___x_2191_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2190_);
lean_ctor_set(v___x_2191_, 1, v___x_2189_);
lean_ctor_set(v___x_2191_, 2, v___x_2188_);
return v___x_2191_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1(void){
_start:
{
lean_object* v___x_2192_; 
v___x_2192_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(lean_object* v_declName_2193_, lean_object* v_ext_2194_, lean_object* v_____r_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
uint8_t v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = 0;
lean_inc(v_declName_2193_);
v___x_2202_ = l_Lean_Meta_Grind_isCasesAttrCandidate(v_declName_2193_, v___x_2201_, v___y_2198_, v___y_2199_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; uint8_t v___x_2204_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref_known(v___x_2202_, 1);
v___x_2204_ = lean_unbox(v_a_2203_);
lean_dec(v_a_2203_);
if (v___x_2204_ == 0)
{
lean_object* v___x_2205_; lean_object* v_a_2206_; uint8_t v___x_2207_; 
v___x_2205_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem___redArg(v_ext_2194_, v_declName_2193_, v___y_2199_);
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = lean_unbox(v_a_2206_);
lean_dec(v_a_2206_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; lean_object* v_a_2209_; uint8_t v___x_2210_; 
lean_inc(v_declName_2193_);
v___x_2208_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isInjectiveTheorem___redArg(v_ext_2194_, v_declName_2193_, v___y_2199_);
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref(v___x_2208_);
v___x_2210_ = lean_unbox(v_a_2209_);
lean_dec(v_a_2209_);
if (v___x_2210_ == 0)
{
lean_object* v___x_2211_; lean_object* v_a_2212_; uint8_t v___x_2213_; 
v___x_2211_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_hasFunCCAttr___redArg(v_ext_2194_, v_declName_2193_, v___y_2199_);
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
lean_dec_ref(v___x_2211_);
v___x_2213_ = lean_unbox(v_a_2212_);
lean_dec(v_a_2212_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; 
v___x_2214_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_2194_, v_declName_2193_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
return v___x_2214_;
}
else
{
lean_object* v___x_2215_; 
v___x_2215_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2194_, v_declName_2193_, v___y_2198_, v___y_2199_);
return v___x_2215_;
}
}
else
{
lean_object* v___x_2216_; 
v___x_2216_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(v_ext_2194_, v_declName_2193_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
return v___x_2216_;
}
}
else
{
lean_object* v___x_2217_; 
v___x_2217_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2194_, v_declName_2193_, v___y_2198_, v___y_2199_);
return v___x_2217_;
}
}
else
{
lean_object* v___x_2218_; 
v___x_2218_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2194_, v_declName_2193_, v___y_2198_, v___y_2199_);
return v___x_2218_;
}
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2226_; 
lean_dec_ref(v_ext_2194_);
lean_dec(v_declName_2193_);
v_a_2219_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2226_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2226_ == 0)
{
v___x_2221_ = v___x_2202_;
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2202_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2226_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v___x_2224_; 
if (v_isShared_2222_ == 0)
{
v___x_2224_ = v___x_2221_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_a_2219_);
v___x_2224_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
return v___x_2224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0___boxed(lean_object* v_declName_2227_, lean_object* v_ext_2228_, lean_object* v_____r_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2227_, v_ext_2228_, v_____r_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(lean_object* v_msgData_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v___x_2242_; lean_object* v_env_2243_; lean_object* v___x_2244_; lean_object* v_mctx_2245_; lean_object* v_lctx_2246_; lean_object* v_options_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2242_ = lean_st_ref_get(v___y_2240_);
v_env_2243_ = lean_ctor_get(v___x_2242_, 0);
lean_inc_ref(v_env_2243_);
lean_dec(v___x_2242_);
v___x_2244_ = lean_st_ref_get(v___y_2238_);
v_mctx_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc_ref(v_mctx_2245_);
lean_dec(v___x_2244_);
v_lctx_2246_ = lean_ctor_get(v___y_2237_, 2);
v_options_2247_ = lean_ctor_get(v___y_2239_, 2);
lean_inc_ref(v_options_2247_);
lean_inc_ref(v_lctx_2246_);
v___x_2248_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2248_, 0, v_env_2243_);
lean_ctor_set(v___x_2248_, 1, v_mctx_2245_);
lean_ctor_set(v___x_2248_, 2, v_lctx_2246_);
lean_ctor_set(v___x_2248_, 3, v_options_2247_);
v___x_2249_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
lean_ctor_set(v___x_2249_, 1, v_msgData_2236_);
v___x_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0___boxed(lean_object* v_msgData_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msgData_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec(v___y_2253_);
lean_dec_ref(v___y_2252_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(lean_object* v_msg_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_ref_2264_; lean_object* v___x_2265_; lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2274_; 
v_ref_2264_ = lean_ctor_get(v___y_2261_, 5);
v___x_2265_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2268_ = v___x_2265_;
v_isShared_2269_ = v_isSharedCheck_2274_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2265_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2274_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___x_2272_; 
lean_inc(v_ref_2264_);
v___x_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2270_, 0, v_ref_2264_);
lean_ctor_set(v___x_2270_, 1, v_a_2266_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set_tag(v___x_2268_, 1);
lean_ctor_set(v___x_2268_, 0, v___x_2270_);
v___x_2272_ = v___x_2268_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg___boxed(lean_object* v_msg_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
return v_res_2281_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2288_; uint64_t v___x_2289_; 
v___x_2288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2289_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2288_);
return v___x_2289_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
uint64_t v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2290_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_2291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0));
v___x_2292_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set_uint64(v___x_2292_, sizeof(void*)*1, v___x_2290_);
return v___x_2292_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2293_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3);
v___x_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
return v___x_2295_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2296_ = lean_box(1);
v___x_2297_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2298_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2299_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
lean_ctor_set(v___x_2299_, 1, v___x_2297_);
lean_ctor_set(v___x_2299_, 2, v___x_2296_);
return v___x_2299_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2302_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2303_ = lean_unsigned_to_nat(0u);
v___x_2304_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
lean_ctor_set(v___x_2304_, 2, v___x_2303_);
lean_ctor_set(v___x_2304_, 3, v___x_2303_);
lean_ctor_set(v___x_2304_, 4, v___x_2302_);
lean_ctor_set(v___x_2304_, 5, v___x_2302_);
lean_ctor_set(v___x_2304_, 6, v___x_2302_);
lean_ctor_set(v___x_2304_, 7, v___x_2302_);
lean_ctor_set(v___x_2304_, 8, v___x_2302_);
lean_ctor_set(v___x_2304_, 9, v___x_2302_);
return v___x_2304_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2306_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
lean_ctor_set(v___x_2306_, 2, v___x_2305_);
lean_ctor_set(v___x_2306_, 3, v___x_2305_);
lean_ctor_set(v___x_2306_, 4, v___x_2305_);
lean_ctor_set(v___x_2306_, 5, v___x_2305_);
return v___x_2306_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2308_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
lean_ctor_set(v___x_2308_, 1, v___x_2307_);
lean_ctor_set(v___x_2308_, 2, v___x_2307_);
lean_ctor_set(v___x_2308_, 3, v___x_2307_);
lean_ctor_set(v___x_2308_, 4, v___x_2307_);
return v___x_2308_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11(void){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10));
v___x_2311_ = l_Lean_stringToMessageData(v___x_2310_);
return v___x_2311_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13(void){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12));
v___x_2314_ = l_Lean_stringToMessageData(v___x_2313_);
return v___x_2314_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15(void){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__14));
v___x_2317_ = l_Lean_stringToMessageData(v___x_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v___x_2318_, lean_object* v_ext_2319_, uint8_t v_showInfo_2320_, lean_object* v_attrName_2321_, lean_object* v_declName_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_){
_start:
{
uint8_t v___x_2326_; uint8_t v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___y_2341_; 
v___x_2326_ = 1;
v___x_2327_ = 0;
v___x_2328_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_2329_ = lean_unsigned_to_nat(0u);
v___x_2330_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2331_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_2332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6));
v___x_2333_ = lean_box(0);
lean_inc(v___x_2318_);
v___x_2334_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2334_, 0, v___x_2328_);
lean_ctor_set(v___x_2334_, 1, v___x_2318_);
lean_ctor_set(v___x_2334_, 2, v___x_2331_);
lean_ctor_set(v___x_2334_, 3, v___x_2332_);
lean_ctor_set(v___x_2334_, 4, v___x_2333_);
lean_ctor_set(v___x_2334_, 5, v___x_2329_);
lean_ctor_set(v___x_2334_, 6, v___x_2333_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*7, v___x_2327_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*7 + 1, v___x_2327_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*7 + 2, v___x_2327_);
lean_ctor_set_uint8(v___x_2334_, sizeof(void*)*7 + 3, v___x_2326_);
v___x_2335_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_2336_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_2337_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_2338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2335_);
lean_ctor_set(v___x_2338_, 1, v___x_2336_);
lean_ctor_set(v___x_2338_, 2, v___x_2318_);
lean_ctor_set(v___x_2338_, 3, v___x_2330_);
lean_ctor_set(v___x_2338_, 4, v___x_2337_);
v___x_2339_ = lean_st_mk_ref(v___x_2338_);
if (v_showInfo_2320_ == 0)
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
lean_dec(v_attrName_2321_);
v___x_2351_ = lean_box(0);
v___x_2352_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2322_, v_ext_2319_, v___x_2351_, v___x_2334_, v___x_2339_, v___y_2323_, v___y_2324_);
lean_dec_ref_known(v___x_2334_, 7);
v___y_2341_ = v___x_2352_;
goto v___jp_2340_;
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
lean_dec(v_declName_2322_);
lean_dec_ref(v_ext_2319_);
v___x_2353_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11);
v___x_2354_ = l_Lean_MessageData_ofName(v_attrName_2321_);
lean_inc_ref(v___x_2354_);
v___x_2355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2353_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v___x_2356_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__13);
v___x_2357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2355_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v___x_2358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
lean_ctor_set(v___x_2358_, 1, v___x_2354_);
v___x_2359_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__15);
v___x_2360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2358_);
lean_ctor_set(v___x_2360_, 1, v___x_2359_);
v___x_2361_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2360_, v___x_2334_, v___x_2339_, v___y_2323_, v___y_2324_);
lean_dec_ref_known(v___x_2334_, 7);
v___y_2341_ = v___x_2361_;
goto v___jp_2340_;
}
v___jp_2340_:
{
if (lean_obj_tag(v___y_2341_) == 0)
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2350_; 
v_a_2342_ = lean_ctor_get(v___y_2341_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___y_2341_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2344_ = v___y_2341_;
v_isShared_2345_ = v_isSharedCheck_2350_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___y_2341_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2350_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2346_ = lean_st_ref_get(v___x_2339_);
lean_dec(v___x_2339_);
lean_dec(v___x_2346_);
if (v_isShared_2345_ == 0)
{
v___x_2348_ = v___x_2344_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2342_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
else
{
lean_dec(v___x_2339_);
return v___y_2341_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v___x_2362_, lean_object* v_ext_2363_, lean_object* v_showInfo_2364_, lean_object* v_attrName_2365_, lean_object* v_declName_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
uint8_t v_showInfo_boxed_2370_; lean_object* v_res_2371_; 
v_showInfo_boxed_2370_ = lean_unbox(v_showInfo_2364_);
v_res_2371_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v___x_2362_, v_ext_2363_, v_showInfo_boxed_2370_, v_attrName_2365_, v_declName_2366_, v___y_2367_, v___y_2368_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_2374_, uint8_t v_attrKind_2375_, uint8_t v_showInfo_2376_, uint8_t v_minIndexable_2377_, lean_object* v_as_x27_2378_, lean_object* v_b_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_){
_start:
{
if (lean_obj_tag(v_as_x27_2378_) == 0)
{
lean_object* v___x_2385_; 
lean_dec_ref(v_ext_2374_);
v___x_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2385_, 0, v_b_2379_);
return v___x_2385_;
}
else
{
lean_object* v_head_2386_; lean_object* v_tail_2387_; lean_object* v___x_2388_; 
v_head_2386_ = lean_ctor_get(v_as_x27_2378_, 0);
v_tail_2387_ = lean_ctor_get(v_as_x27_2378_, 1);
v___x_2388_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2383_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v___x_2390_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v_head_2386_);
lean_inc_ref(v_ext_2374_);
v___x_2391_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2374_, v_head_2386_, v_attrKind_2375_, v___x_2390_, v_a_2389_, v_showInfo_2376_, v_minIndexable_2377_, v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v___x_2392_; 
lean_dec_ref_known(v___x_2391_, 1);
v___x_2392_ = lean_box(0);
v_as_x27_2378_ = v_tail_2387_;
v_b_2379_ = v___x_2392_;
goto _start;
}
else
{
lean_dec_ref(v_ext_2374_);
return v___x_2391_;
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_dec_ref(v_ext_2374_);
v_a_2394_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2388_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2388_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_2402_, lean_object* v_attrKind_2403_, lean_object* v_showInfo_2404_, lean_object* v_minIndexable_2405_, lean_object* v_as_x27_2406_, lean_object* v_b_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
uint8_t v_attrKind_boxed_2413_; uint8_t v_showInfo_boxed_2414_; uint8_t v_minIndexable_boxed_2415_; lean_object* v_res_2416_; 
v_attrKind_boxed_2413_ = lean_unbox(v_attrKind_2403_);
v_showInfo_boxed_2414_ = lean_unbox(v_showInfo_2404_);
v_minIndexable_boxed_2415_ = lean_unbox(v_minIndexable_2405_);
v_res_2416_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2402_, v_attrKind_boxed_2413_, v_showInfo_boxed_2414_, v_minIndexable_boxed_2415_, v_as_x27_2406_, v_b_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v_as_x27_2406_);
return v_res_2416_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2418_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_2419_ = l_Lean_stringToMessageData(v___x_2418_);
return v___x_2419_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_2422_ = l_Lean_stringToMessageData(v___x_2421_);
return v___x_2422_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_2425_ = l_Lean_stringToMessageData(v___x_2424_);
return v___x_2425_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_2428_ = l_Lean_stringToMessageData(v___x_2427_);
return v___x_2428_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11(void){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10));
v___x_2434_ = l_Lean_stringToMessageData(v___x_2433_);
return v___x_2434_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13(void){
_start:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12));
v___x_2437_ = l_Lean_stringToMessageData(v___x_2436_);
return v___x_2437_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14));
v___x_2440_ = l_Lean_stringToMessageData(v___x_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_stx_2441_, lean_object* v_ext_2442_, lean_object* v_declName_2443_, uint8_t v_attrKind_2444_, uint8_t v_showInfo_2445_, uint8_t v_minIndexable_2446_, uint8_t v___x_2447_, lean_object* v_attrName_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___x_2482_; 
v___x_2482_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_2441_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2482_, 1);
switch(lean_obj_tag(v_a_2483_))
{
case 0:
{
lean_object* v_k_2484_; 
lean_dec(v_attrName_2448_);
lean_dec(v_stx_2441_);
v_k_2484_ = lean_ctor_get(v_a_2483_, 0);
lean_inc(v_k_2484_);
lean_dec_ref_known(v_a_2483_, 1);
if (lean_obj_tag(v_k_2484_) == 9)
{
lean_object* v___x_2485_; 
lean_dec(v_declName_2443_);
lean_dec_ref(v_ext_2442_);
v___x_2485_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_2451_, v___y_2452_);
return v___x_2485_;
}
else
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2452_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; lean_object* v___x_2488_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref_known(v___x_2486_, 1);
v___x_2488_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2442_, v_declName_2443_, v_attrKind_2444_, v_k_2484_, v_a_2487_, v_showInfo_2445_, v_minIndexable_2446_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2488_;
}
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_dec(v_k_2484_);
lean_dec(v_declName_2443_);
lean_dec_ref(v_ext_2442_);
v_a_2489_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2486_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2486_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
}
case 1:
{
uint8_t v_eager_2497_; lean_object* v___x_2498_; 
lean_dec(v_attrName_2448_);
lean_dec(v_stx_2441_);
v_eager_2497_ = lean_ctor_get_uint8(v_a_2483_, 0);
lean_dec_ref_known(v_a_2483_, 0);
v___x_2498_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2442_, v_declName_2443_, v_eager_2497_, v_attrKind_2444_, v___y_2451_, v___y_2452_);
return v___x_2498_;
}
case 2:
{
lean_object* v___x_2499_; 
lean_dec(v_stx_2441_);
lean_inc(v_declName_2443_);
v___x_2499_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_2443_, v___x_2447_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_a_2500_; 
v_a_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_a_2500_);
lean_dec_ref_known(v___x_2499_, 1);
if (lean_obj_tag(v_a_2500_) == 1)
{
lean_object* v_val_2501_; lean_object* v_ctors_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_dec(v_attrName_2448_);
lean_dec(v_declName_2443_);
v_val_2501_ = lean_ctor_get(v_a_2500_, 0);
lean_inc(v_val_2501_);
lean_dec_ref_known(v_a_2500_, 1);
v_ctors_2502_ = lean_ctor_get(v_val_2501_, 4);
lean_inc(v_ctors_2502_);
lean_dec(v_val_2501_);
v___x_2503_ = lean_box(0);
v___x_2504_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2442_, v_attrKind_2444_, v_showInfo_2445_, v_minIndexable_2446_, v_ctors_2502_, v___x_2503_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v_ctors_2502_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2511_ == 0)
{
lean_object* v_unused_2512_; 
v_unused_2512_ = lean_ctor_get(v___x_2504_, 0);
lean_dec(v_unused_2512_);
v___x_2506_ = v___x_2504_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_dec(v___x_2504_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2503_);
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2503_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
else
{
return v___x_2504_;
}
}
else
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_dec(v_a_2500_);
lean_dec_ref(v_ext_2442_);
v___x_2513_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3);
v___x_2514_ = l_Lean_MessageData_ofName(v_attrName_2448_);
v___x_2515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
v___x_2516_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_2517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2515_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = l_Lean_MessageData_ofConstName(v_declName_2443_, v___x_2447_);
v___x_2519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2517_);
lean_ctor_set(v___x_2519_, 1, v___x_2518_);
v___x_2520_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_2521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2519_);
lean_ctor_set(v___x_2521_, 1, v___x_2520_);
v___x_2522_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2521_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2522_;
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec(v_attrName_2448_);
lean_dec(v_declName_2443_);
lean_dec_ref(v_ext_2442_);
v_a_2523_ = lean_ctor_get(v___x_2499_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2499_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2499_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2499_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
case 3:
{
lean_object* v___x_2531_; 
lean_dec(v_attrName_2448_);
lean_inc(v_declName_2443_);
v___x_2531_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_2443_, v___x_2447_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_a_2532_);
lean_dec_ref_known(v___x_2531_, 1);
if (lean_obj_tag(v_a_2532_) == 1)
{
lean_object* v_val_2533_; lean_object* v___x_2534_; 
lean_dec(v_declName_2443_);
lean_dec(v_stx_2441_);
v_val_2533_ = lean_ctor_get(v_a_2532_, 0);
lean_inc_n(v_val_2533_, 2);
lean_dec_ref_known(v_a_2532_, 1);
lean_inc_ref(v_ext_2442_);
v___x_2534_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2442_, v_val_2533_, v___x_2447_, v_attrKind_2444_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v___x_2535_; 
lean_dec_ref_known(v___x_2534_, 1);
v___x_2535_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_2533_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2556_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2538_ = v___x_2535_;
v_isShared_2539_ = v_isSharedCheck_2556_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2535_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2556_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
if (lean_obj_tag(v_a_2536_) == 1)
{
lean_object* v_val_2540_; lean_object* v_ctors_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
lean_del_object(v___x_2538_);
v_val_2540_ = lean_ctor_get(v_a_2536_, 0);
lean_inc(v_val_2540_);
lean_dec_ref_known(v_a_2536_, 1);
v_ctors_2541_ = lean_ctor_get(v_val_2540_, 4);
lean_inc(v_ctors_2541_);
lean_dec(v_val_2540_);
v___x_2542_ = lean_box(0);
v___x_2543_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2442_, v_attrKind_2444_, v_showInfo_2445_, v_minIndexable_2446_, v_ctors_2541_, v___x_2542_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v_ctors_2541_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2550_ == 0)
{
lean_object* v_unused_2551_; 
v_unused_2551_ = lean_ctor_get(v___x_2543_, 0);
lean_dec(v_unused_2551_);
v___x_2545_ = v___x_2543_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_dec(v___x_2543_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 0, v___x_2542_);
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2542_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
else
{
return v___x_2543_;
}
}
else
{
lean_object* v___x_2552_; lean_object* v___x_2554_; 
lean_dec(v_a_2536_);
lean_dec_ref(v_ext_2442_);
v___x_2552_ = lean_box(0);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 0, v___x_2552_);
v___x_2554_ = v___x_2538_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec_ref(v_ext_2442_);
v_a_2557_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2535_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2535_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
else
{
lean_dec(v_val_2533_);
lean_dec_ref(v_ext_2442_);
return v___x_2534_;
}
}
else
{
lean_object* v___x_2565_; 
lean_dec(v_a_2532_);
v___x_2565_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2452_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; lean_object* v___x_2567_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref_known(v___x_2565_, 1);
v___x_2567_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_2442_, v_stx_2441_, v_declName_2443_, v_attrKind_2444_, v_a_2566_, v_minIndexable_2446_, v_showInfo_2445_, v___x_2447_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2567_;
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec(v_declName_2443_);
lean_dec_ref(v_ext_2442_);
lean_dec(v_stx_2441_);
v_a_2568_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2565_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2565_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
}
else
{
lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2583_; 
lean_dec(v_declName_2443_);
lean_dec_ref(v_ext_2442_);
lean_dec(v_stx_2441_);
v_a_2576_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2583_ == 0)
{
v___x_2578_ = v___x_2531_;
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_dec(v___x_2531_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2583_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2581_; 
if (v_isShared_2579_ == 0)
{
v___x_2581_ = v___x_2578_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_a_2576_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
case 4:
{
lean_object* v___x_2584_; 
lean_dec(v_attrName_2448_);
lean_dec(v_stx_2441_);
v___x_2584_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2442_, v_declName_2443_, v_attrKind_2444_, v___y_2451_, v___y_2452_);
return v___x_2584_;
}
case 5:
{
lean_object* v_prio_2585_; lean_object* v___x_2586_; uint8_t v___x_2587_; 
lean_dec_ref(v_ext_2442_);
lean_dec(v_stx_2441_);
v_prio_2585_ = lean_ctor_get(v_a_2483_, 0);
lean_inc(v_prio_2585_);
lean_dec_ref_known(v_a_2483_, 1);
v___x_2586_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2587_ = lean_name_eq(v_attrName_2448_, v___x_2586_);
lean_dec(v_attrName_2448_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
lean_dec(v_prio_2585_);
lean_dec(v_declName_2443_);
v___x_2588_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11);
v___x_2589_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2588_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2589_;
}
else
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_2443_, v_attrKind_2444_, v_prio_2585_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2590_;
}
}
case 6:
{
lean_object* v___x_2591_; 
lean_dec(v_attrName_2448_);
lean_dec(v_stx_2441_);
v___x_2591_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_2442_, v_declName_2443_, v_attrKind_2444_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2591_;
}
case 7:
{
lean_object* v___x_2592_; 
lean_dec(v_attrName_2448_);
lean_dec(v_stx_2441_);
v___x_2592_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2442_, v_declName_2443_, v_attrKind_2444_, v___y_2451_, v___y_2452_);
return v___x_2592_;
}
case 8:
{
uint8_t v_post_2593_; uint8_t v_inv_2594_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
lean_dec_ref(v_ext_2442_);
lean_dec(v_stx_2441_);
v_post_2593_ = lean_ctor_get_uint8(v_a_2483_, 0);
v_inv_2594_ = lean_ctor_get_uint8(v_a_2483_, 1);
lean_dec_ref_known(v_a_2483_, 0);
v___x_2603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2604_ = lean_name_eq(v_attrName_2448_, v___x_2603_);
lean_dec(v_attrName_2448_);
if (v___x_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v___x_2606_; 
lean_dec(v_declName_2443_);
v___x_2605_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13);
v___x_2606_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2605_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2606_;
}
else
{
v___y_2596_ = v___y_2449_;
v___y_2597_ = v___y_2450_;
v___y_2598_ = v___y_2451_;
v___y_2599_ = v___y_2452_;
goto v___jp_2595_;
}
v___jp_2595_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; 
v___x_2600_ = l_Lean_Meta_Grind_normExt;
v___x_2601_ = lean_unsigned_to_nat(1000u);
v___x_2602_ = l_Lean_Meta_addSimpTheorem(v___x_2600_, v_declName_2443_, v_post_2593_, v_inv_2594_, v_attrKind_2444_, v___x_2601_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_);
return v___x_2602_;
}
}
default: 
{
lean_object* v___x_2607_; uint8_t v___x_2608_; 
lean_dec_ref(v_ext_2442_);
lean_dec(v_stx_2441_);
v___x_2607_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2608_ = lean_name_eq(v_attrName_2448_, v___x_2607_);
lean_dec(v_attrName_2448_);
if (v___x_2608_ == 0)
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_dec(v_declName_2443_);
v___x_2609_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15);
v___x_2610_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2609_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
return v___x_2610_;
}
else
{
v___y_2455_ = v___y_2449_;
v___y_2456_ = v___y_2450_;
v___y_2457_ = v___y_2451_;
v___y_2458_ = v___y_2452_;
goto v___jp_2454_;
}
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec(v_attrName_2448_);
lean_dec(v_declName_2443_);
lean_dec_ref(v_ext_2442_);
lean_dec(v_stx_2441_);
v_a_2611_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2482_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2482_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
v___jp_2454_:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2459_ = l_Lean_Meta_Grind_normExt;
v___x_2460_ = lean_unsigned_to_nat(1000u);
v___x_2461_ = l_Lean_Meta_addDeclToUnfold(v___x_2459_, v_declName_2443_, v___x_2447_, v___x_2447_, v___x_2460_, v_attrKind_2444_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2473_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2464_ = v___x_2461_;
v_isShared_2465_ = v_isSharedCheck_2473_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2461_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2473_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
uint8_t v___x_2466_; 
v___x_2466_ = lean_unbox(v_a_2462_);
lean_dec(v_a_2462_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
lean_del_object(v___x_2464_);
v___x_2467_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_2468_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2467_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
return v___x_2468_;
}
else
{
lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2469_ = lean_box(0);
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 0, v___x_2469_);
v___x_2471_ = v___x_2464_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
else
{
lean_object* v_a_2474_; lean_object* v___x_2476_; uint8_t v_isShared_2477_; uint8_t v_isSharedCheck_2481_; 
v_a_2474_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2481_ == 0)
{
v___x_2476_ = v___x_2461_;
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
else
{
lean_inc(v_a_2474_);
lean_dec(v___x_2461_);
v___x_2476_ = lean_box(0);
v_isShared_2477_ = v_isSharedCheck_2481_;
goto v_resetjp_2475_;
}
v_resetjp_2475_:
{
lean_object* v___x_2479_; 
if (v_isShared_2477_ == 0)
{
v___x_2479_ = v___x_2476_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_a_2474_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_stx_2619_, lean_object* v_ext_2620_, lean_object* v_declName_2621_, lean_object* v_attrKind_2622_, lean_object* v_showInfo_2623_, lean_object* v_minIndexable_2624_, lean_object* v___x_2625_, lean_object* v_attrName_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
uint8_t v_attrKind_boxed_2632_; uint8_t v_showInfo_boxed_2633_; uint8_t v_minIndexable_boxed_2634_; uint8_t v___x_15301__boxed_2635_; lean_object* v_res_2636_; 
v_attrKind_boxed_2632_ = lean_unbox(v_attrKind_2622_);
v_showInfo_boxed_2633_ = lean_unbox(v_showInfo_2623_);
v_minIndexable_boxed_2634_ = lean_unbox(v_minIndexable_2624_);
v___x_15301__boxed_2635_ = lean_unbox(v___x_2625_);
v_res_2636_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_stx_2619_, v_ext_2620_, v_declName_2621_, v_attrKind_boxed_2632_, v_showInfo_boxed_2633_, v_minIndexable_boxed_2634_, v___x_15301__boxed_2635_, v_attrName_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
return v_res_2636_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0(void){
_start:
{
lean_object* v___x_2637_; double v___x_2638_; 
v___x_2637_ = lean_unsigned_to_nat(0u);
v___x_2638_ = lean_float_of_nat(v___x_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object* v_cls_2642_, lean_object* v_msg_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_ref_2649_; lean_object* v___x_2650_; lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2695_; 
v_ref_2649_ = lean_ctor_get(v___y_2646_, 5);
v___x_2650_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
v_isSharedCheck_2695_ = !lean_is_exclusive(v___x_2650_);
if (v_isSharedCheck_2695_ == 0)
{
v___x_2653_ = v___x_2650_;
v_isShared_2654_ = v_isSharedCheck_2695_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2650_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2695_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2655_; lean_object* v_traceState_2656_; lean_object* v_env_2657_; lean_object* v_nextMacroScope_2658_; lean_object* v_ngen_2659_; lean_object* v_auxDeclNGen_2660_; lean_object* v_cache_2661_; lean_object* v_messages_2662_; lean_object* v_infoState_2663_; lean_object* v_snapshotTasks_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2694_; 
v___x_2655_ = lean_st_ref_take(v___y_2647_);
v_traceState_2656_ = lean_ctor_get(v___x_2655_, 4);
v_env_2657_ = lean_ctor_get(v___x_2655_, 0);
v_nextMacroScope_2658_ = lean_ctor_get(v___x_2655_, 1);
v_ngen_2659_ = lean_ctor_get(v___x_2655_, 2);
v_auxDeclNGen_2660_ = lean_ctor_get(v___x_2655_, 3);
v_cache_2661_ = lean_ctor_get(v___x_2655_, 5);
v_messages_2662_ = lean_ctor_get(v___x_2655_, 6);
v_infoState_2663_ = lean_ctor_get(v___x_2655_, 7);
v_snapshotTasks_2664_ = lean_ctor_get(v___x_2655_, 8);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2666_ = v___x_2655_;
v_isShared_2667_ = v_isSharedCheck_2694_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_snapshotTasks_2664_);
lean_inc(v_infoState_2663_);
lean_inc(v_messages_2662_);
lean_inc(v_cache_2661_);
lean_inc(v_traceState_2656_);
lean_inc(v_auxDeclNGen_2660_);
lean_inc(v_ngen_2659_);
lean_inc(v_nextMacroScope_2658_);
lean_inc(v_env_2657_);
lean_dec(v___x_2655_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2694_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
uint64_t v_tid_2668_; lean_object* v_traces_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2693_; 
v_tid_2668_ = lean_ctor_get_uint64(v_traceState_2656_, sizeof(void*)*1);
v_traces_2669_ = lean_ctor_get(v_traceState_2656_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_traceState_2656_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2671_ = v_traceState_2656_;
v_isShared_2672_ = v_isSharedCheck_2693_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_traces_2669_);
lean_dec(v_traceState_2656_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2693_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2673_; double v___x_2674_; uint8_t v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2673_ = lean_box(0);
v___x_2674_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_2675_ = 0;
v___x_2676_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2677_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2677_, 0, v_cls_2642_);
lean_ctor_set(v___x_2677_, 1, v___x_2673_);
lean_ctor_set(v___x_2677_, 2, v___x_2676_);
lean_ctor_set_float(v___x_2677_, sizeof(void*)*3, v___x_2674_);
lean_ctor_set_float(v___x_2677_, sizeof(void*)*3 + 8, v___x_2674_);
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*3 + 16, v___x_2675_);
v___x_2678_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_2679_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2679_, 0, v___x_2677_);
lean_ctor_set(v___x_2679_, 1, v_a_2651_);
lean_ctor_set(v___x_2679_, 2, v___x_2678_);
lean_inc(v_ref_2649_);
v___x_2680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2680_, 0, v_ref_2649_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = l_Lean_PersistentArray_push___redArg(v_traces_2669_, v___x_2680_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 0, v___x_2681_);
v___x_2683_ = v___x_2671_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2681_);
lean_ctor_set_uint64(v_reuseFailAlloc_2692_, sizeof(void*)*1, v_tid_2668_);
v___x_2683_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2685_; 
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 4, v___x_2683_);
v___x_2685_ = v___x_2666_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_env_2657_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v_nextMacroScope_2658_);
lean_ctor_set(v_reuseFailAlloc_2691_, 2, v_ngen_2659_);
lean_ctor_set(v_reuseFailAlloc_2691_, 3, v_auxDeclNGen_2660_);
lean_ctor_set(v_reuseFailAlloc_2691_, 4, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2691_, 5, v_cache_2661_);
lean_ctor_set(v_reuseFailAlloc_2691_, 6, v_messages_2662_);
lean_ctor_set(v_reuseFailAlloc_2691_, 7, v_infoState_2663_);
lean_ctor_set(v_reuseFailAlloc_2691_, 8, v_snapshotTasks_2664_);
v___x_2685_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2686_ = lean_st_ref_set(v___y_2647_, v___x_2685_);
v___x_2687_ = lean_box(0);
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 0, v___x_2687_);
v___x_2689_ = v___x_2653_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object* v_cls_2696_, lean_object* v_msg_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2696_, v_msg_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
return v_res_2703_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(lean_object* v_keys_2704_, lean_object* v_i_2705_, lean_object* v_k_2706_){
_start:
{
lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2707_ = lean_array_get_size(v_keys_2704_);
v___x_2708_ = lean_nat_dec_lt(v_i_2705_, v___x_2707_);
if (v___x_2708_ == 0)
{
lean_dec(v_i_2705_);
return v___x_2708_;
}
else
{
lean_object* v_k_x27_2709_; uint8_t v___x_2710_; 
v_k_x27_2709_ = lean_array_fget_borrowed(v_keys_2704_, v_i_2705_);
v___x_2710_ = l_Lean_instBEqExtraModUse_beq(v_k_2706_, v_k_x27_2709_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; lean_object* v___x_2712_; 
v___x_2711_ = lean_unsigned_to_nat(1u);
v___x_2712_ = lean_nat_add(v_i_2705_, v___x_2711_);
lean_dec(v_i_2705_);
v_i_2705_ = v___x_2712_;
goto _start;
}
else
{
lean_dec(v_i_2705_);
return v___x_2710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg___boxed(lean_object* v_keys_2714_, lean_object* v_i_2715_, lean_object* v_k_2716_){
_start:
{
uint8_t v_res_2717_; lean_object* v_r_2718_; 
v_res_2717_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_2714_, v_i_2715_, v_k_2716_);
lean_dec_ref(v_k_2716_);
lean_dec_ref(v_keys_2714_);
v_r_2718_ = lean_box(v_res_2717_);
return v_r_2718_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2719_, size_t v_x_2720_, lean_object* v_x_2721_){
_start:
{
if (lean_obj_tag(v_x_2719_) == 0)
{
lean_object* v_es_2722_; lean_object* v___x_2723_; size_t v___x_2724_; size_t v___x_2725_; lean_object* v_j_2726_; lean_object* v___x_2727_; 
v_es_2722_ = lean_ctor_get(v_x_2719_, 0);
v___x_2723_ = lean_box(2);
v___x_2724_ = ((size_t)31ULL);
v___x_2725_ = lean_usize_land(v_x_2720_, v___x_2724_);
v_j_2726_ = lean_usize_to_nat(v___x_2725_);
v___x_2727_ = lean_array_get_borrowed(v___x_2723_, v_es_2722_, v_j_2726_);
lean_dec(v_j_2726_);
switch(lean_obj_tag(v___x_2727_))
{
case 0:
{
lean_object* v_key_2728_; uint8_t v___x_2729_; 
v_key_2728_ = lean_ctor_get(v___x_2727_, 0);
v___x_2729_ = l_Lean_instBEqExtraModUse_beq(v_x_2721_, v_key_2728_);
return v___x_2729_;
}
case 1:
{
lean_object* v_node_2730_; size_t v___x_2731_; size_t v___x_2732_; 
v_node_2730_ = lean_ctor_get(v___x_2727_, 0);
v___x_2731_ = ((size_t)5ULL);
v___x_2732_ = lean_usize_shift_right(v_x_2720_, v___x_2731_);
v_x_2719_ = v_node_2730_;
v_x_2720_ = v___x_2732_;
goto _start;
}
default: 
{
uint8_t v___x_2734_; 
v___x_2734_ = 0;
return v___x_2734_;
}
}
}
else
{
lean_object* v_ks_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; 
v_ks_2735_ = lean_ctor_get(v_x_2719_, 0);
v___x_2736_ = lean_unsigned_to_nat(0u);
v___x_2737_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_ks_2735_, v___x_2736_, v_x_2721_);
return v___x_2737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2738_, lean_object* v_x_2739_, lean_object* v_x_2740_){
_start:
{
size_t v_x_15795__boxed_2741_; uint8_t v_res_2742_; lean_object* v_r_2743_; 
v_x_15795__boxed_2741_ = lean_unbox_usize(v_x_2739_);
lean_dec(v_x_2739_);
v_res_2742_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2738_, v_x_15795__boxed_2741_, v_x_2740_);
lean_dec_ref(v_x_2740_);
lean_dec_ref(v_x_2738_);
v_r_2743_ = lean_box(v_res_2742_);
return v_r_2743_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2744_, lean_object* v_x_2745_){
_start:
{
uint64_t v___x_2746_; size_t v___x_2747_; uint8_t v___x_2748_; 
v___x_2746_ = l_Lean_instHashableExtraModUse_hash(v_x_2745_);
v___x_2747_ = lean_uint64_to_usize(v___x_2746_);
v___x_2748_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2744_, v___x_2747_, v_x_2745_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_2749_, lean_object* v_x_2750_){
_start:
{
uint8_t v_res_2751_; lean_object* v_r_2752_; 
v_res_2751_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_2749_, v_x_2750_);
lean_dec_ref(v_x_2750_);
lean_dec_ref(v_x_2749_);
v_r_2752_ = lean_box(v_res_2751_);
return v_r_2752_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2755_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1));
v___x_2756_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0));
v___x_2757_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2756_, v___x_2755_);
return v___x_2757_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5));
v___x_2763_ = l_Lean_stringToMessageData(v___x_2762_);
return v___x_2763_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7));
v___x_2766_ = l_Lean_stringToMessageData(v___x_2765_);
return v___x_2766_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_2768_ = l_Lean_stringToMessageData(v___x_2767_);
return v___x_2768_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12(void){
_start:
{
lean_object* v_cls_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v_cls_2772_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_2773_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11));
v___x_2774_ = l_Lean_Name_append(v___x_2773_, v_cls_2772_);
return v___x_2774_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14(void){
_start:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13));
v___x_2777_ = l_Lean_stringToMessageData(v___x_2776_);
return v___x_2777_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16(void){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___x_2780_ = l_Lean_stringToMessageData(v___x_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v_mod_2785_, uint8_t v_isMeta_2786_, lean_object* v_hint_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___x_2793_; lean_object* v_env_2794_; uint8_t v_isExporting_2795_; lean_object* v___x_2796_; lean_object* v_env_2797_; lean_object* v___x_2798_; lean_object* v_entry_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___x_2845_; uint8_t v___x_2846_; 
v___x_2793_ = lean_st_ref_get(v___y_2791_);
v_env_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc_ref(v_env_2794_);
lean_dec(v___x_2793_);
v_isExporting_2795_ = lean_ctor_get_uint8(v_env_2794_, sizeof(void*)*8);
lean_dec_ref(v_env_2794_);
v___x_2796_ = lean_st_ref_get(v___y_2791_);
v_env_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc_ref(v_env_2797_);
lean_dec(v___x_2796_);
v___x_2798_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_2785_);
v_entry_2799_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2799_, 0, v_mod_2785_);
lean_ctor_set_uint8(v_entry_2799_, sizeof(void*)*1, v_isExporting_2795_);
lean_ctor_set_uint8(v_entry_2799_, sizeof(void*)*1 + 1, v_isMeta_2786_);
v___x_2800_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2801_ = lean_box(1);
v___x_2802_ = lean_box(0);
v___x_2845_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2798_, v___x_2800_, v_env_2797_, v___x_2801_, v___x_2802_);
v___x_2846_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_2845_, v_entry_2799_);
lean_dec(v___x_2845_);
if (v___x_2846_ == 0)
{
lean_object* v_options_2847_; uint8_t v_hasTrace_2848_; 
v_options_2847_ = lean_ctor_get(v___y_2790_, 2);
v_hasTrace_2848_ = lean_ctor_get_uint8(v_options_2847_, sizeof(void*)*1);
if (v_hasTrace_2848_ == 0)
{
lean_dec(v_hint_2787_);
lean_dec(v_mod_2785_);
v___y_2804_ = v___y_2789_;
v___y_2805_ = v___y_2791_;
goto v___jp_2803_;
}
else
{
lean_object* v_inheritedTraceOptions_2849_; lean_object* v_cls_2850_; lean_object* v___y_2852_; lean_object* v___y_2853_; lean_object* v___y_2857_; lean_object* v___y_2858_; lean_object* v___x_2870_; uint8_t v___x_2871_; 
v_inheritedTraceOptions_2849_ = lean_ctor_get(v___y_2790_, 13);
v_cls_2850_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_2870_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
v___x_2871_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2849_, v_options_2847_, v___x_2870_);
if (v___x_2871_ == 0)
{
lean_dec(v_hint_2787_);
lean_dec(v_mod_2785_);
v___y_2804_ = v___y_2789_;
v___y_2805_ = v___y_2791_;
goto v___jp_2803_;
}
else
{
lean_object* v___x_2872_; lean_object* v___y_2874_; 
v___x_2872_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
if (v_isExporting_2795_ == 0)
{
lean_object* v___x_2881_; 
v___x_2881_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19));
v___y_2874_ = v___x_2881_;
goto v___jp_2873_;
}
else
{
lean_object* v___x_2882_; 
v___x_2882_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20));
v___y_2874_ = v___x_2882_;
goto v___jp_2873_;
}
v___jp_2873_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; 
lean_inc_ref(v___y_2874_);
v___x_2875_ = l_Lean_stringToMessageData(v___y_2874_);
v___x_2876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2872_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
v___x_2877_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16);
v___x_2878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2876_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
if (v_isMeta_2786_ == 0)
{
lean_object* v___x_2879_; 
v___x_2879_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_2857_ = v___x_2878_;
v___y_2858_ = v___x_2879_;
goto v___jp_2856_;
}
else
{
lean_object* v___x_2880_; 
v___x_2880_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_2857_ = v___x_2878_;
v___y_2858_ = v___x_2880_;
goto v___jp_2856_;
}
}
}
v___jp_2851_:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___y_2852_);
lean_ctor_set(v___x_2854_, 1, v___y_2853_);
v___x_2855_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_2850_, v___x_2854_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_dec_ref_known(v___x_2855_, 1);
v___y_2804_ = v___y_2789_;
v___y_2805_ = v___y_2791_;
goto v___jp_2803_;
}
else
{
lean_dec_ref_known(v_entry_2799_, 1);
return v___x_2855_;
}
}
v___jp_2856_:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; 
lean_inc_ref(v___y_2858_);
v___x_2859_ = l_Lean_stringToMessageData(v___y_2858_);
v___x_2860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2860_, 0, v___y_2857_);
lean_ctor_set(v___x_2860_, 1, v___x_2859_);
v___x_2861_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_2862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2862_, 0, v___x_2860_);
lean_ctor_set(v___x_2862_, 1, v___x_2861_);
v___x_2863_ = l_Lean_MessageData_ofName(v_mod_2785_);
v___x_2864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2862_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = l_Lean_Name_isAnonymous(v_hint_2787_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2866_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_2867_ = l_Lean_MessageData_ofName(v_hint_2787_);
v___x_2868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___y_2852_ = v___x_2864_;
v___y_2853_ = v___x_2868_;
goto v___jp_2851_;
}
else
{
lean_object* v___x_2869_; 
lean_dec(v_hint_2787_);
v___x_2869_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_2852_ = v___x_2864_;
v___y_2853_ = v___x_2869_;
goto v___jp_2851_;
}
}
}
}
else
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
lean_dec_ref_known(v_entry_2799_, 1);
lean_dec(v_hint_2787_);
lean_dec(v_mod_2785_);
v___x_2883_ = lean_box(0);
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
return v___x_2884_;
}
v___jp_2803_:
{
lean_object* v___x_2806_; lean_object* v_toEnvExtension_2807_; lean_object* v_env_2808_; lean_object* v_nextMacroScope_2809_; lean_object* v_ngen_2810_; lean_object* v_auxDeclNGen_2811_; lean_object* v_traceState_2812_; lean_object* v_messages_2813_; lean_object* v_infoState_2814_; lean_object* v_snapshotTasks_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2843_; 
v___x_2806_ = lean_st_ref_take(v___y_2805_);
v_toEnvExtension_2807_ = lean_ctor_get(v___x_2800_, 0);
v_env_2808_ = lean_ctor_get(v___x_2806_, 0);
v_nextMacroScope_2809_ = lean_ctor_get(v___x_2806_, 1);
v_ngen_2810_ = lean_ctor_get(v___x_2806_, 2);
v_auxDeclNGen_2811_ = lean_ctor_get(v___x_2806_, 3);
v_traceState_2812_ = lean_ctor_get(v___x_2806_, 4);
v_messages_2813_ = lean_ctor_get(v___x_2806_, 6);
v_infoState_2814_ = lean_ctor_get(v___x_2806_, 7);
v_snapshotTasks_2815_ = lean_ctor_get(v___x_2806_, 8);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v___x_2806_, 5);
lean_dec(v_unused_2844_);
v___x_2817_ = v___x_2806_;
v_isShared_2818_ = v_isSharedCheck_2843_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_snapshotTasks_2815_);
lean_inc(v_infoState_2814_);
lean_inc(v_messages_2813_);
lean_inc(v_traceState_2812_);
lean_inc(v_auxDeclNGen_2811_);
lean_inc(v_ngen_2810_);
lean_inc(v_nextMacroScope_2809_);
lean_inc(v_env_2808_);
lean_dec(v___x_2806_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2843_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v_asyncMode_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2823_; 
v_asyncMode_2819_ = lean_ctor_get(v_toEnvExtension_2807_, 2);
v___x_2820_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2800_, v_env_2808_, v_entry_2799_, v_asyncMode_2819_, v___x_2802_);
v___x_2821_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 5, v___x_2821_);
lean_ctor_set(v___x_2817_, 0, v___x_2820_);
v___x_2823_ = v___x_2817_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2820_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v_nextMacroScope_2809_);
lean_ctor_set(v_reuseFailAlloc_2842_, 2, v_ngen_2810_);
lean_ctor_set(v_reuseFailAlloc_2842_, 3, v_auxDeclNGen_2811_);
lean_ctor_set(v_reuseFailAlloc_2842_, 4, v_traceState_2812_);
lean_ctor_set(v_reuseFailAlloc_2842_, 5, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2842_, 6, v_messages_2813_);
lean_ctor_set(v_reuseFailAlloc_2842_, 7, v_infoState_2814_);
lean_ctor_set(v_reuseFailAlloc_2842_, 8, v_snapshotTasks_2815_);
v___x_2823_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v_mctx_2826_; lean_object* v_zetaDeltaFVarIds_2827_; lean_object* v_postponed_2828_; lean_object* v_diag_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2840_; 
v___x_2824_ = lean_st_ref_set(v___y_2805_, v___x_2823_);
v___x_2825_ = lean_st_ref_take(v___y_2804_);
v_mctx_2826_ = lean_ctor_get(v___x_2825_, 0);
v_zetaDeltaFVarIds_2827_ = lean_ctor_get(v___x_2825_, 2);
v_postponed_2828_ = lean_ctor_get(v___x_2825_, 3);
v_diag_2829_ = lean_ctor_get(v___x_2825_, 4);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2840_ == 0)
{
lean_object* v_unused_2841_; 
v_unused_2841_ = lean_ctor_get(v___x_2825_, 1);
lean_dec(v_unused_2841_);
v___x_2831_ = v___x_2825_;
v_isShared_2832_ = v_isSharedCheck_2840_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_diag_2829_);
lean_inc(v_postponed_2828_);
lean_inc(v_zetaDeltaFVarIds_2827_);
lean_inc(v_mctx_2826_);
lean_dec(v___x_2825_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2840_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2833_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 1, v___x_2833_);
v___x_2835_ = v___x_2831_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_mctx_2826_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v_zetaDeltaFVarIds_2827_);
lean_ctor_set(v_reuseFailAlloc_2839_, 3, v_postponed_2828_);
lean_ctor_set(v_reuseFailAlloc_2839_, 4, v_diag_2829_);
v___x_2835_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2836_ = lean_st_ref_set(v___y_2804_, v___x_2835_);
v___x_2837_ = lean_box(0);
v___x_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2837_);
return v___x_2838_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v_mod_2885_, lean_object* v_isMeta_2886_, lean_object* v_hint_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
uint8_t v_isMeta_boxed_2893_; lean_object* v_res_2894_; 
v_isMeta_boxed_2893_ = lean_unbox(v_isMeta_2886_);
v_res_2894_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_mod_2885_, v_isMeta_boxed_2893_, v_hint_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(lean_object* v_a_2895_, lean_object* v_x_2896_){
_start:
{
if (lean_obj_tag(v_x_2896_) == 0)
{
lean_object* v___x_2897_; 
v___x_2897_ = lean_box(0);
return v___x_2897_;
}
else
{
lean_object* v_key_2898_; lean_object* v_value_2899_; lean_object* v_tail_2900_; uint8_t v___x_2901_; 
v_key_2898_ = lean_ctor_get(v_x_2896_, 0);
v_value_2899_ = lean_ctor_get(v_x_2896_, 1);
v_tail_2900_ = lean_ctor_get(v_x_2896_, 2);
v___x_2901_ = lean_name_eq(v_key_2898_, v_a_2895_);
if (v___x_2901_ == 0)
{
v_x_2896_ = v_tail_2900_;
goto _start;
}
else
{
lean_object* v___x_2903_; 
lean_inc(v_value_2899_);
v___x_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2903_, 0, v_value_2899_);
return v___x_2903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_a_2904_, lean_object* v_x_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2904_, v_x_2905_);
lean_dec(v_x_2905_);
lean_dec(v_a_2904_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object* v_m_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_buckets_2909_; lean_object* v___x_2910_; uint64_t v___y_2912_; 
v_buckets_2909_ = lean_ctor_get(v_m_2907_, 1);
v___x_2910_ = lean_array_get_size(v_buckets_2909_);
if (lean_obj_tag(v_a_2908_) == 0)
{
uint64_t v___x_2926_; 
v___x_2926_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_2912_ = v___x_2926_;
goto v___jp_2911_;
}
else
{
uint64_t v_hash_2927_; 
v_hash_2927_ = lean_ctor_get_uint64(v_a_2908_, sizeof(void*)*2);
v___y_2912_ = v_hash_2927_;
goto v___jp_2911_;
}
v___jp_2911_:
{
uint64_t v___x_2913_; uint64_t v___x_2914_; uint64_t v_fold_2915_; uint64_t v___x_2916_; uint64_t v___x_2917_; uint64_t v___x_2918_; size_t v___x_2919_; size_t v___x_2920_; size_t v___x_2921_; size_t v___x_2922_; size_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2913_ = 32ULL;
v___x_2914_ = lean_uint64_shift_right(v___y_2912_, v___x_2913_);
v_fold_2915_ = lean_uint64_xor(v___y_2912_, v___x_2914_);
v___x_2916_ = 16ULL;
v___x_2917_ = lean_uint64_shift_right(v_fold_2915_, v___x_2916_);
v___x_2918_ = lean_uint64_xor(v_fold_2915_, v___x_2917_);
v___x_2919_ = lean_uint64_to_usize(v___x_2918_);
v___x_2920_ = lean_usize_of_nat(v___x_2910_);
v___x_2921_ = ((size_t)1ULL);
v___x_2922_ = lean_usize_sub(v___x_2920_, v___x_2921_);
v___x_2923_ = lean_usize_land(v___x_2919_, v___x_2922_);
v___x_2924_ = lean_array_uget_borrowed(v_buckets_2909_, v___x_2923_);
v___x_2925_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_2908_, v___x_2924_);
return v___x_2925_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object* v_m_2928_, lean_object* v_a_2929_){
_start:
{
lean_object* v_res_2930_; 
v_res_2930_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_2928_, v_a_2929_);
lean_dec(v_a_2929_);
lean_dec_ref(v_m_2928_);
return v_res_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v___x_2931_, lean_object* v_declName_2932_, lean_object* v_as_2933_, size_t v_sz_2934_, size_t v_i_2935_, lean_object* v_b_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
uint8_t v___x_2942_; 
v___x_2942_ = lean_usize_dec_lt(v_i_2935_, v_sz_2934_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; 
lean_dec(v_declName_2932_);
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v_b_2936_);
return v___x_2943_;
}
else
{
lean_object* v___x_2944_; lean_object* v_modules_2945_; lean_object* v___x_2946_; lean_object* v_a_2947_; lean_object* v___x_2948_; lean_object* v_toImport_2949_; lean_object* v_module_2950_; uint8_t v___x_2951_; lean_object* v___x_2952_; 
v___x_2944_ = l_Lean_Environment_header(v___x_2931_);
v_modules_2945_ = lean_ctor_get(v___x_2944_, 3);
lean_inc_ref(v_modules_2945_);
lean_dec_ref(v___x_2944_);
v___x_2946_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2947_ = lean_array_uget_borrowed(v_as_2933_, v_i_2935_);
v___x_2948_ = lean_array_get(v___x_2946_, v_modules_2945_, v_a_2947_);
lean_dec_ref(v_modules_2945_);
v_toImport_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc_ref(v_toImport_2949_);
lean_dec(v___x_2948_);
v_module_2950_ = lean_ctor_get(v_toImport_2949_, 0);
lean_inc(v_module_2950_);
lean_dec_ref(v_toImport_2949_);
v___x_2951_ = 0;
lean_inc(v_declName_2932_);
v___x_2952_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_2950_, v___x_2951_, v_declName_2932_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v___x_2953_; size_t v___x_2954_; size_t v___x_2955_; 
lean_dec_ref_known(v___x_2952_, 1);
v___x_2953_ = lean_box(0);
v___x_2954_ = ((size_t)1ULL);
v___x_2955_ = lean_usize_add(v_i_2935_, v___x_2954_);
v_i_2935_ = v___x_2955_;
v_b_2936_ = v___x_2953_;
goto _start;
}
else
{
lean_dec(v_declName_2932_);
return v___x_2952_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v___x_2957_, lean_object* v_declName_2958_, lean_object* v_as_2959_, lean_object* v_sz_2960_, lean_object* v_i_2961_, lean_object* v_b_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
size_t v_sz_boxed_2968_; size_t v_i_boxed_2969_; lean_object* v_res_2970_; 
v_sz_boxed_2968_ = lean_unbox_usize(v_sz_2960_);
lean_dec(v_sz_2960_);
v_i_boxed_2969_ = lean_unbox_usize(v_i_2961_);
lean_dec(v_i_2961_);
v_res_2970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v___x_2957_, v_declName_2958_, v_as_2959_, v_sz_boxed_2968_, v_i_boxed_2969_, v_b_2962_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
lean_dec(v___y_2966_);
lean_dec_ref(v___y_2965_);
lean_dec(v___y_2964_);
lean_dec_ref(v___y_2963_);
lean_dec_ref(v_as_2959_);
lean_dec_ref(v___x_2957_);
return v_res_2970_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2973_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___x_2974_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0));
v___x_2975_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2974_, v___x_2973_);
return v___x_2975_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_2978_, uint8_t v_isMeta_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_){
_start:
{
lean_object* v___x_2985_; lean_object* v_env_2989_; lean_object* v___y_2991_; lean_object* v___x_3004_; 
v___x_2985_ = lean_st_ref_get(v___y_2983_);
v_env_2989_ = lean_ctor_get(v___x_2985_, 0);
lean_inc_ref(v_env_2989_);
lean_dec(v___x_2985_);
v___x_3004_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2989_, v_declName_2978_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_dec_ref(v_env_2989_);
lean_dec(v_declName_2978_);
goto v___jp_2986_;
}
else
{
lean_object* v_val_3005_; lean_object* v___x_3006_; lean_object* v_modules_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v_val_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_val_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3006_ = l_Lean_Environment_header(v_env_2989_);
v_modules_3007_ = lean_ctor_get(v___x_3006_, 3);
lean_inc_ref(v_modules_3007_);
lean_dec_ref(v___x_3006_);
v___x_3008_ = lean_array_get_size(v_modules_3007_);
v___x_3009_ = lean_nat_dec_lt(v_val_3005_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_dec_ref(v_modules_3007_);
lean_dec(v_val_3005_);
lean_dec_ref(v_env_2989_);
lean_dec(v_declName_2978_);
goto v___jp_2986_;
}
else
{
lean_object* v___x_3010_; lean_object* v_env_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___y_3015_; 
v___x_3010_ = lean_st_ref_get(v___y_2983_);
v_env_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc_ref(v_env_3011_);
lean_dec(v___x_3010_);
v___x_3012_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3013_ = lean_array_fget(v_modules_3007_, v_val_3005_);
lean_dec(v_val_3005_);
lean_dec_ref(v_modules_3007_);
if (v_isMeta_2979_ == 0)
{
lean_dec_ref(v_env_3011_);
v___y_3015_ = v_isMeta_2979_;
goto v___jp_3014_;
}
else
{
uint8_t v___x_3026_; 
lean_inc(v_declName_2978_);
v___x_3026_ = l_Lean_isMarkedMeta(v_env_3011_, v_declName_2978_);
if (v___x_3026_ == 0)
{
v___y_3015_ = v_isMeta_2979_;
goto v___jp_3014_;
}
else
{
uint8_t v___x_3027_; 
v___x_3027_ = 0;
v___y_3015_ = v___x_3027_;
goto v___jp_3014_;
}
}
v___jp_3014_:
{
lean_object* v_toImport_3016_; lean_object* v_module_3017_; lean_object* v___x_3018_; 
v_toImport_3016_ = lean_ctor_get(v___x_3013_, 0);
lean_inc_ref(v_toImport_3016_);
lean_dec(v___x_3013_);
v_module_3017_ = lean_ctor_get(v_toImport_3016_, 0);
lean_inc(v_module_3017_);
lean_dec_ref(v_toImport_3016_);
lean_inc(v_declName_2978_);
v___x_3018_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3017_, v___y_3015_, v_declName_2978_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
lean_dec_ref_known(v___x_3018_, 1);
v___x_3019_ = l_Lean_indirectModUseExt;
v___x_3020_ = lean_box(1);
v___x_3021_ = lean_box(0);
lean_inc_ref(v_env_2989_);
v___x_3022_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3012_, v___x_3019_, v_env_2989_, v___x_3020_, v___x_3021_);
v___x_3023_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3022_, v_declName_2978_);
lean_dec(v___x_3022_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v___x_3024_; 
v___x_3024_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_2991_ = v___x_3024_;
goto v___jp_2990_;
}
else
{
lean_object* v_val_3025_; 
v_val_3025_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_val_3025_);
lean_dec_ref_known(v___x_3023_, 1);
v___y_2991_ = v_val_3025_;
goto v___jp_2990_;
}
}
else
{
lean_dec_ref(v_env_2989_);
lean_dec(v_declName_2978_);
return v___x_3018_;
}
}
}
}
v___jp_2986_:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = lean_box(0);
v___x_2988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2988_, 0, v___x_2987_);
return v___x_2988_;
}
v___jp_2990_:
{
lean_object* v___x_2992_; size_t v_sz_2993_; size_t v___x_2994_; lean_object* v___x_2995_; 
v___x_2992_ = lean_box(0);
v_sz_2993_ = lean_array_size(v___y_2991_);
v___x_2994_ = ((size_t)0ULL);
v___x_2995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_env_2989_, v_declName_2978_, v___y_2991_, v_sz_2993_, v___x_2994_, v___x_2992_, v___y_2980_, v___y_2981_, v___y_2982_, v___y_2983_);
lean_dec_ref(v___y_2991_);
lean_dec_ref(v_env_2989_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3002_ == 0)
{
lean_object* v_unused_3003_; 
v_unused_3003_ = lean_ctor_get(v___x_2995_, 0);
lean_dec(v_unused_3003_);
v___x_2997_ = v___x_2995_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_dec(v___x_2995_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v___x_2992_);
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2992_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
else
{
return v___x_2995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_3028_, lean_object* v_isMeta_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_){
_start:
{
uint8_t v_isMeta_boxed_3035_; lean_object* v_res_3036_; 
v_isMeta_boxed_3035_ = lean_unbox(v_isMeta_3029_);
v_res_3036_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3028_, v_isMeta_boxed_3035_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
lean_dec(v___y_3033_);
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object* v___y_3037_, uint8_t v_isExporting_3038_, lean_object* v___x_3039_, lean_object* v___y_3040_, lean_object* v___x_3041_, lean_object* v_a_x3f_3042_){
_start:
{
lean_object* v___x_3044_; lean_object* v_env_3045_; lean_object* v_nextMacroScope_3046_; lean_object* v_ngen_3047_; lean_object* v_auxDeclNGen_3048_; lean_object* v_traceState_3049_; lean_object* v_messages_3050_; lean_object* v_infoState_3051_; lean_object* v_snapshotTasks_3052_; lean_object* v___x_3054_; uint8_t v_isShared_3055_; uint8_t v_isSharedCheck_3077_; 
v___x_3044_ = lean_st_ref_take(v___y_3037_);
v_env_3045_ = lean_ctor_get(v___x_3044_, 0);
v_nextMacroScope_3046_ = lean_ctor_get(v___x_3044_, 1);
v_ngen_3047_ = lean_ctor_get(v___x_3044_, 2);
v_auxDeclNGen_3048_ = lean_ctor_get(v___x_3044_, 3);
v_traceState_3049_ = lean_ctor_get(v___x_3044_, 4);
v_messages_3050_ = lean_ctor_get(v___x_3044_, 6);
v_infoState_3051_ = lean_ctor_get(v___x_3044_, 7);
v_snapshotTasks_3052_ = lean_ctor_get(v___x_3044_, 8);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3077_ == 0)
{
lean_object* v_unused_3078_; 
v_unused_3078_ = lean_ctor_get(v___x_3044_, 5);
lean_dec(v_unused_3078_);
v___x_3054_ = v___x_3044_;
v_isShared_3055_ = v_isSharedCheck_3077_;
goto v_resetjp_3053_;
}
else
{
lean_inc(v_snapshotTasks_3052_);
lean_inc(v_infoState_3051_);
lean_inc(v_messages_3050_);
lean_inc(v_traceState_3049_);
lean_inc(v_auxDeclNGen_3048_);
lean_inc(v_ngen_3047_);
lean_inc(v_nextMacroScope_3046_);
lean_inc(v_env_3045_);
lean_dec(v___x_3044_);
v___x_3054_ = lean_box(0);
v_isShared_3055_ = v_isSharedCheck_3077_;
goto v_resetjp_3053_;
}
v_resetjp_3053_:
{
lean_object* v___x_3056_; lean_object* v___x_3058_; 
v___x_3056_ = l_Lean_Environment_setExporting(v_env_3045_, v_isExporting_3038_);
if (v_isShared_3055_ == 0)
{
lean_ctor_set(v___x_3054_, 5, v___x_3039_);
lean_ctor_set(v___x_3054_, 0, v___x_3056_);
v___x_3058_ = v___x_3054_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3056_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_nextMacroScope_3046_);
lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_ngen_3047_);
lean_ctor_set(v_reuseFailAlloc_3076_, 3, v_auxDeclNGen_3048_);
lean_ctor_set(v_reuseFailAlloc_3076_, 4, v_traceState_3049_);
lean_ctor_set(v_reuseFailAlloc_3076_, 5, v___x_3039_);
lean_ctor_set(v_reuseFailAlloc_3076_, 6, v_messages_3050_);
lean_ctor_set(v_reuseFailAlloc_3076_, 7, v_infoState_3051_);
lean_ctor_set(v_reuseFailAlloc_3076_, 8, v_snapshotTasks_3052_);
v___x_3058_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v_mctx_3061_; lean_object* v_zetaDeltaFVarIds_3062_; lean_object* v_postponed_3063_; lean_object* v_diag_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3074_; 
v___x_3059_ = lean_st_ref_set(v___y_3037_, v___x_3058_);
v___x_3060_ = lean_st_ref_take(v___y_3040_);
v_mctx_3061_ = lean_ctor_get(v___x_3060_, 0);
v_zetaDeltaFVarIds_3062_ = lean_ctor_get(v___x_3060_, 2);
v_postponed_3063_ = lean_ctor_get(v___x_3060_, 3);
v_diag_3064_ = lean_ctor_get(v___x_3060_, 4);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3074_ == 0)
{
lean_object* v_unused_3075_; 
v_unused_3075_ = lean_ctor_get(v___x_3060_, 1);
lean_dec(v_unused_3075_);
v___x_3066_ = v___x_3060_;
v_isShared_3067_ = v_isSharedCheck_3074_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_diag_3064_);
lean_inc(v_postponed_3063_);
lean_inc(v_zetaDeltaFVarIds_3062_);
lean_inc(v_mctx_3061_);
lean_dec(v___x_3060_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3074_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 1, v___x_3041_);
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_mctx_3061_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3073_, 2, v_zetaDeltaFVarIds_3062_);
lean_ctor_set(v_reuseFailAlloc_3073_, 3, v_postponed_3063_);
lean_ctor_set(v_reuseFailAlloc_3073_, 4, v_diag_3064_);
v___x_3069_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3070_ = lean_st_ref_set(v___y_3040_, v___x_3069_);
v___x_3071_ = lean_box(0);
v___x_3072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
return v___x_3072_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object* v___y_3079_, lean_object* v_isExporting_3080_, lean_object* v___x_3081_, lean_object* v___y_3082_, lean_object* v___x_3083_, lean_object* v_a_x3f_3084_, lean_object* v___y_3085_){
_start:
{
uint8_t v_isExporting_boxed_3086_; lean_object* v_res_3087_; 
v_isExporting_boxed_3086_ = lean_unbox(v_isExporting_3080_);
v_res_3087_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3079_, v_isExporting_boxed_3086_, v___x_3081_, v___y_3082_, v___x_3083_, v_a_x3f_3084_);
lean_dec(v_a_x3f_3084_);
lean_dec(v___y_3082_);
lean_dec(v___y_3079_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object* v_x_3088_, uint8_t v_isExporting_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v___x_3095_; lean_object* v_env_3096_; uint8_t v_isExporting_3097_; lean_object* v___x_3098_; lean_object* v_env_3099_; lean_object* v_nextMacroScope_3100_; lean_object* v_ngen_3101_; lean_object* v_auxDeclNGen_3102_; lean_object* v_traceState_3103_; lean_object* v_messages_3104_; lean_object* v_infoState_3105_; lean_object* v_snapshotTasks_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3160_; 
v___x_3095_ = lean_st_ref_get(v___y_3093_);
v_env_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc_ref(v_env_3096_);
lean_dec(v___x_3095_);
v_isExporting_3097_ = lean_ctor_get_uint8(v_env_3096_, sizeof(void*)*8);
lean_dec_ref(v_env_3096_);
v___x_3098_ = lean_st_ref_take(v___y_3093_);
v_env_3099_ = lean_ctor_get(v___x_3098_, 0);
v_nextMacroScope_3100_ = lean_ctor_get(v___x_3098_, 1);
v_ngen_3101_ = lean_ctor_get(v___x_3098_, 2);
v_auxDeclNGen_3102_ = lean_ctor_get(v___x_3098_, 3);
v_traceState_3103_ = lean_ctor_get(v___x_3098_, 4);
v_messages_3104_ = lean_ctor_get(v___x_3098_, 6);
v_infoState_3105_ = lean_ctor_get(v___x_3098_, 7);
v_snapshotTasks_3106_ = lean_ctor_get(v___x_3098_, 8);
v_isSharedCheck_3160_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; 
v_unused_3161_ = lean_ctor_get(v___x_3098_, 5);
lean_dec(v_unused_3161_);
v___x_3108_ = v___x_3098_;
v_isShared_3109_ = v_isSharedCheck_3160_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_snapshotTasks_3106_);
lean_inc(v_infoState_3105_);
lean_inc(v_messages_3104_);
lean_inc(v_traceState_3103_);
lean_inc(v_auxDeclNGen_3102_);
lean_inc(v_ngen_3101_);
lean_inc(v_nextMacroScope_3100_);
lean_inc(v_env_3099_);
lean_dec(v___x_3098_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3160_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3110_ = l_Lean_Environment_setExporting(v_env_3099_, v_isExporting_3089_);
v___x_3111_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 5, v___x_3111_);
lean_ctor_set(v___x_3108_, 0, v___x_3110_);
v___x_3113_ = v___x_3108_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3110_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v_nextMacroScope_3100_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v_ngen_3101_);
lean_ctor_set(v_reuseFailAlloc_3159_, 3, v_auxDeclNGen_3102_);
lean_ctor_set(v_reuseFailAlloc_3159_, 4, v_traceState_3103_);
lean_ctor_set(v_reuseFailAlloc_3159_, 5, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3159_, 6, v_messages_3104_);
lean_ctor_set(v_reuseFailAlloc_3159_, 7, v_infoState_3105_);
lean_ctor_set(v_reuseFailAlloc_3159_, 8, v_snapshotTasks_3106_);
v___x_3113_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v_mctx_3116_; lean_object* v_zetaDeltaFVarIds_3117_; lean_object* v_postponed_3118_; lean_object* v_diag_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3157_; 
v___x_3114_ = lean_st_ref_set(v___y_3093_, v___x_3113_);
v___x_3115_ = lean_st_ref_take(v___y_3091_);
v_mctx_3116_ = lean_ctor_get(v___x_3115_, 0);
v_zetaDeltaFVarIds_3117_ = lean_ctor_get(v___x_3115_, 2);
v_postponed_3118_ = lean_ctor_get(v___x_3115_, 3);
v_diag_3119_ = lean_ctor_get(v___x_3115_, 4);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3115_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; 
v_unused_3158_ = lean_ctor_get(v___x_3115_, 1);
lean_dec(v_unused_3158_);
v___x_3121_ = v___x_3115_;
v_isShared_3122_ = v_isSharedCheck_3157_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_diag_3119_);
lean_inc(v_postponed_3118_);
lean_inc(v_zetaDeltaFVarIds_3117_);
lean_inc(v_mctx_3116_);
lean_dec(v___x_3115_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3157_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; lean_object* v___x_3125_; 
v___x_3123_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 1, v___x_3123_);
v___x_3125_ = v___x_3121_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_mctx_3116_);
lean_ctor_set(v_reuseFailAlloc_3156_, 1, v___x_3123_);
lean_ctor_set(v_reuseFailAlloc_3156_, 2, v_zetaDeltaFVarIds_3117_);
lean_ctor_set(v_reuseFailAlloc_3156_, 3, v_postponed_3118_);
lean_ctor_set(v_reuseFailAlloc_3156_, 4, v_diag_3119_);
v___x_3125_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
lean_object* v___x_3126_; lean_object* v_r_3127_; 
v___x_3126_ = lean_st_ref_set(v___y_3091_, v___x_3125_);
lean_inc(v___y_3093_);
lean_inc_ref(v___y_3092_);
lean_inc(v___y_3091_);
lean_inc_ref(v___y_3090_);
v_r_3127_ = lean_apply_5(v_x_3088_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_, lean_box(0));
if (lean_obj_tag(v_r_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3144_; 
v_a_3128_ = lean_ctor_get(v_r_3127_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v_r_3127_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3130_ = v_r_3127_;
v_isShared_3131_ = v_isSharedCheck_3144_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v_r_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3144_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
lean_inc(v_a_3128_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set_tag(v___x_3130_, 1);
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
lean_object* v___x_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
v___x_3134_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3093_, v_isExporting_3097_, v___x_3111_, v___y_3091_, v___x_3123_, v___x_3133_);
lean_dec_ref(v___x_3133_);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3141_ == 0)
{
lean_object* v_unused_3142_; 
v_unused_3142_ = lean_ctor_get(v___x_3134_, 0);
lean_dec(v_unused_3142_);
v___x_3136_ = v___x_3134_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_dec(v___x_3134_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 0, v_a_3128_);
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3128_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
v_a_3145_ = lean_ctor_get(v_r_3127_, 0);
lean_inc(v_a_3145_);
lean_dec_ref_known(v_r_3127_, 1);
v___x_3146_ = lean_box(0);
v___x_3147_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3093_, v_isExporting_3097_, v___x_3111_, v___y_3091_, v___x_3123_, v___x_3146_);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3154_ == 0)
{
lean_object* v_unused_3155_; 
v_unused_3155_ = lean_ctor_get(v___x_3147_, 0);
lean_dec(v_unused_3155_);
v___x_3149_ = v___x_3147_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_dec(v___x_3147_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
lean_ctor_set_tag(v___x_3149_, 1);
lean_ctor_set(v___x_3149_, 0, v_a_3145_);
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3145_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object* v_x_3162_, lean_object* v_isExporting_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
uint8_t v_isExporting_boxed_3169_; lean_object* v_res_3170_; 
v_isExporting_boxed_3169_ = lean_unbox(v_isExporting_3163_);
v_res_3170_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3162_, v_isExporting_boxed_3169_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_3171_, uint8_t v_when_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
if (v_when_3172_ == 0)
{
lean_object* v___x_3178_; 
lean_inc(v___y_3176_);
lean_inc_ref(v___y_3175_);
lean_inc(v___y_3174_);
lean_inc_ref(v___y_3173_);
v___x_3178_ = lean_apply_5(v_x_3171_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, lean_box(0));
return v___x_3178_;
}
else
{
uint8_t v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = 0;
v___x_3180_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3171_, v___x_3179_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
return v___x_3180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_3181_, lean_object* v_when_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
uint8_t v_when_boxed_3188_; lean_object* v_res_3189_; 
v_when_boxed_3188_ = lean_unbox(v_when_3182_);
v_res_3189_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3181_, v_when_boxed_3188_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v___x_3190_, lean_object* v_ext_3191_, uint8_t v_showInfo_3192_, uint8_t v_minIndexable_3193_, lean_object* v_attrName_3194_, lean_object* v_declName_3195_, lean_object* v_stx_3196_, uint8_t v_attrKind_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_){
_start:
{
uint8_t v___x_3201_; uint8_t v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___y_3218_; lean_object* v___x_3228_; 
v___x_3201_ = 0;
v___x_3202_ = 1;
v___x_3203_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3204_ = lean_unsigned_to_nat(32u);
v___x_3205_ = lean_mk_empty_array_with_capacity(v___x_3204_);
lean_dec_ref(v___x_3205_);
v___x_3206_ = lean_unsigned_to_nat(0u);
v___x_3207_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_3208_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_3209_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6));
v___x_3210_ = lean_box(0);
lean_inc(v___x_3190_);
v___x_3211_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3211_, 0, v___x_3203_);
lean_ctor_set(v___x_3211_, 1, v___x_3190_);
lean_ctor_set(v___x_3211_, 2, v___x_3208_);
lean_ctor_set(v___x_3211_, 3, v___x_3209_);
lean_ctor_set(v___x_3211_, 4, v___x_3210_);
lean_ctor_set(v___x_3211_, 5, v___x_3206_);
lean_ctor_set(v___x_3211_, 6, v___x_3210_);
lean_ctor_set_uint8(v___x_3211_, sizeof(void*)*7, v___x_3201_);
lean_ctor_set_uint8(v___x_3211_, sizeof(void*)*7 + 1, v___x_3201_);
lean_ctor_set_uint8(v___x_3211_, sizeof(void*)*7 + 2, v___x_3201_);
lean_ctor_set_uint8(v___x_3211_, sizeof(void*)*7 + 3, v___x_3202_);
v___x_3212_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7);
v___x_3213_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_3214_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9);
v___x_3215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3212_);
lean_ctor_set(v___x_3215_, 1, v___x_3213_);
lean_ctor_set(v___x_3215_, 2, v___x_3190_);
lean_ctor_set(v___x_3215_, 3, v___x_3207_);
lean_ctor_set(v___x_3215_, 4, v___x_3214_);
v___x_3216_ = lean_st_mk_ref(v___x_3215_);
lean_inc(v_declName_3195_);
v___x_3228_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3195_, v___x_3201_, v___x_3211_, v___x_3216_, v___y_3198_, v___y_3199_);
if (lean_obj_tag(v___x_3228_) == 0)
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___f_3233_; lean_object* v___x_3234_; 
lean_dec_ref_known(v___x_3228_, 1);
v___x_3229_ = lean_box(v_attrKind_3197_);
v___x_3230_ = lean_box(v_showInfo_3192_);
v___x_3231_ = lean_box(v_minIndexable_3193_);
v___x_3232_ = lean_box(v___x_3201_);
v___f_3233_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_3233_, 0, v_stx_3196_);
lean_closure_set(v___f_3233_, 1, v_ext_3191_);
lean_closure_set(v___f_3233_, 2, v_declName_3195_);
lean_closure_set(v___f_3233_, 3, v___x_3229_);
lean_closure_set(v___f_3233_, 4, v___x_3230_);
lean_closure_set(v___f_3233_, 5, v___x_3231_);
lean_closure_set(v___f_3233_, 6, v___x_3232_);
lean_closure_set(v___f_3233_, 7, v_attrName_3194_);
v___x_3234_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_3233_, v___x_3202_, v___x_3211_, v___x_3216_, v___y_3198_, v___y_3199_);
lean_dec_ref_known(v___x_3211_, 7);
v___y_3218_ = v___x_3234_;
goto v___jp_3217_;
}
else
{
lean_dec_ref_known(v___x_3211_, 7);
lean_dec(v_stx_3196_);
lean_dec(v_declName_3195_);
lean_dec(v_attrName_3194_);
lean_dec_ref(v_ext_3191_);
v___y_3218_ = v___x_3228_;
goto v___jp_3217_;
}
v___jp_3217_:
{
if (lean_obj_tag(v___y_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3227_; 
v_a_3219_ = lean_ctor_get(v___y_3218_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___y_3218_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3221_ = v___y_3218_;
v_isShared_3222_ = v_isSharedCheck_3227_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_a_3219_);
lean_dec(v___y_3218_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3227_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3223_ = lean_st_ref_get(v___x_3216_);
lean_dec(v___x_3216_);
lean_dec(v___x_3223_);
if (v_isShared_3222_ == 0)
{
v___x_3225_ = v___x_3221_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3219_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
else
{
lean_dec(v___x_3216_);
return v___y_3218_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v___x_3235_, lean_object* v_ext_3236_, lean_object* v_showInfo_3237_, lean_object* v_minIndexable_3238_, lean_object* v_attrName_3239_, lean_object* v_declName_3240_, lean_object* v_stx_3241_, lean_object* v_attrKind_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
uint8_t v_showInfo_boxed_3246_; uint8_t v_minIndexable_boxed_3247_; uint8_t v_attrKind_boxed_3248_; lean_object* v_res_3249_; 
v_showInfo_boxed_3246_ = lean_unbox(v_showInfo_3237_);
v_minIndexable_boxed_3247_ = lean_unbox(v_minIndexable_3238_);
v_attrKind_boxed_3248_ = lean_unbox(v_attrKind_3242_);
v_res_3249_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v___x_3235_, v_ext_3236_, v_showInfo_boxed_3246_, v_minIndexable_boxed_3247_, v_attrName_3239_, v_declName_3240_, v_stx_3241_, v_attrKind_boxed_3248_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_3272_, uint8_t v_minIndexable_3273_, uint8_t v_showInfo_3274_, lean_object* v_ext_3275_, lean_object* v_ref_3276_){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___f_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___f_3283_; lean_object* v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3329_; 
v___x_3278_ = lean_box(1);
v___x_3279_ = lean_box(v_showInfo_3274_);
lean_inc_n(v_attrName_3272_, 2);
lean_inc_ref(v_ext_3275_);
v___f_3280_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_3280_, 0, v___x_3278_);
lean_closure_set(v___f_3280_, 1, v_ext_3275_);
lean_closure_set(v___f_3280_, 2, v___x_3279_);
lean_closure_set(v___f_3280_, 3, v_attrName_3272_);
v___x_3281_ = lean_box(v_showInfo_3274_);
v___x_3282_ = lean_box(v_minIndexable_3273_);
v___f_3283_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_3283_, 0, v___x_3278_);
lean_closure_set(v___f_3283_, 1, v_ext_3275_);
lean_closure_set(v___f_3283_, 2, v___x_3281_);
lean_closure_set(v___f_3283_, 3, v___x_3282_);
lean_closure_set(v___f_3283_, 4, v_attrName_3272_);
if (v_minIndexable_3273_ == 0)
{
if (v_showInfo_3274_ == 0)
{
lean_inc(v_attrName_3272_);
v___y_3329_ = v_attrName_3272_;
goto v___jp_3328_;
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_3272_);
v___x_3358_ = lean_name_append_after(v_attrName_3272_, v___x_3357_);
v___y_3329_ = v___x_3358_;
goto v___jp_3328_;
}
}
else
{
if (v_showInfo_3274_ == 0)
{
lean_object* v___x_3359_; lean_object* v___x_3360_; 
v___x_3359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_3272_);
v___x_3360_ = lean_name_append_after(v_attrName_3272_, v___x_3359_);
v___y_3329_ = v___x_3360_;
goto v___jp_3328_;
}
else
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_3272_);
v___x_3362_ = lean_name_append_after(v_attrName_3272_, v___x_3361_);
v___y_3329_ = v___x_3362_;
goto v___jp_3328_;
}
}
v___jp_3284_:
{
lean_object* v___x_3287_; uint8_t v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; uint8_t v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3287_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_3288_ = 1;
v___x_3289_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3272_, v___x_3288_);
v___x_3290_ = lean_string_append(v___x_3287_, v___x_3289_);
v___x_3291_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_3292_ = lean_string_append(v___x_3290_, v___x_3291_);
v___x_3293_ = lean_string_append(v___x_3292_, v___x_3289_);
v___x_3294_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_3295_ = lean_string_append(v___x_3293_, v___x_3294_);
v___x_3296_ = lean_string_append(v___x_3295_, v___x_3289_);
v___x_3297_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_3298_ = lean_string_append(v___x_3296_, v___x_3297_);
v___x_3299_ = lean_string_append(v___x_3298_, v___x_3289_);
v___x_3300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_3301_ = lean_string_append(v___x_3299_, v___x_3300_);
v___x_3302_ = lean_string_append(v___x_3301_, v___x_3289_);
v___x_3303_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_3304_ = lean_string_append(v___x_3302_, v___x_3303_);
v___x_3305_ = lean_string_append(v___x_3304_, v___x_3289_);
v___x_3306_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_3307_ = lean_string_append(v___x_3305_, v___x_3306_);
v___x_3308_ = lean_string_append(v___x_3307_, v___x_3289_);
v___x_3309_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_3310_ = lean_string_append(v___x_3308_, v___x_3309_);
v___x_3311_ = lean_string_append(v___x_3310_, v___x_3289_);
v___x_3312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_3313_ = lean_string_append(v___x_3311_, v___x_3312_);
v___x_3314_ = lean_string_append(v___x_3313_, v___x_3289_);
v___x_3315_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_3316_ = lean_string_append(v___x_3314_, v___x_3315_);
v___x_3317_ = lean_string_append(v___x_3316_, v___x_3289_);
v___x_3318_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_3319_ = lean_string_append(v___x_3317_, v___x_3318_);
v___x_3320_ = lean_string_append(v___x_3319_, v___x_3289_);
lean_dec_ref(v___x_3289_);
v___x_3321_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_3322_ = lean_string_append(v___x_3320_, v___x_3321_);
v___x_3323_ = lean_string_append(v___y_3286_, v___x_3322_);
lean_dec_ref(v___x_3322_);
v___x_3324_ = 1;
v___x_3325_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3325_, 0, v_ref_3276_);
lean_ctor_set(v___x_3325_, 1, v___y_3285_);
lean_ctor_set(v___x_3325_, 2, v___x_3323_);
lean_ctor_set_uint8(v___x_3325_, sizeof(void*)*3, v___x_3324_);
v___x_3326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
lean_ctor_set(v___x_3326_, 1, v___f_3283_);
lean_ctor_set(v___x_3326_, 2, v___f_3280_);
v___x_3327_ = l_Lean_registerBuiltinAttribute(v___x_3326_);
return v___x_3327_;
}
v___jp_3328_:
{
if (v_minIndexable_3273_ == 0)
{
if (v_showInfo_3274_ == 0)
{
lean_object* v___x_3330_; uint8_t v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3330_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_3331_ = 1;
lean_inc(v_attrName_3272_);
v___x_3332_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3272_, v___x_3331_);
v___x_3333_ = lean_string_append(v___x_3330_, v___x_3332_);
lean_dec_ref(v___x_3332_);
v___x_3334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_3335_ = lean_string_append(v___x_3333_, v___x_3334_);
v___y_3285_ = v___y_3329_;
v___y_3286_ = v___x_3335_;
goto v___jp_3284_;
}
else
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3336_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3272_);
v___x_3337_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3272_, v_showInfo_3274_);
v___x_3338_ = lean_string_append(v___x_3336_, v___x_3337_);
v___x_3339_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_3340_ = lean_string_append(v___x_3338_, v___x_3339_);
v___x_3341_ = lean_string_append(v___x_3340_, v___x_3337_);
lean_dec_ref(v___x_3337_);
v___x_3342_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_3343_ = lean_string_append(v___x_3341_, v___x_3342_);
v___y_3285_ = v___y_3329_;
v___y_3286_ = v___x_3343_;
goto v___jp_3284_;
}
}
else
{
if (v_showInfo_3274_ == 0)
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3344_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3272_);
v___x_3345_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3272_, v_minIndexable_3273_);
v___x_3346_ = lean_string_append(v___x_3344_, v___x_3345_);
lean_dec_ref(v___x_3345_);
v___x_3347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_3348_ = lean_string_append(v___x_3346_, v___x_3347_);
v___y_3285_ = v___y_3329_;
v___y_3286_ = v___x_3348_;
goto v___jp_3284_;
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3272_);
v___x_3350_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3272_, v_showInfo_3274_);
v___x_3351_ = lean_string_append(v___x_3349_, v___x_3350_);
v___x_3352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_3353_ = lean_string_append(v___x_3351_, v___x_3352_);
v___x_3354_ = lean_string_append(v___x_3353_, v___x_3350_);
lean_dec_ref(v___x_3350_);
v___x_3355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_3356_ = lean_string_append(v___x_3354_, v___x_3355_);
v___y_3285_ = v___y_3329_;
v___y_3286_ = v___x_3356_;
goto v___jp_3284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_3363_, lean_object* v_minIndexable_3364_, lean_object* v_showInfo_3365_, lean_object* v_ext_3366_, lean_object* v_ref_3367_, lean_object* v_a_3368_){
_start:
{
uint8_t v_minIndexable_boxed_3369_; uint8_t v_showInfo_boxed_3370_; lean_object* v_res_3371_; 
v_minIndexable_boxed_3369_ = lean_unbox(v_minIndexable_3364_);
v_showInfo_boxed_3370_ = lean_unbox(v_showInfo_3365_);
v_res_3371_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3363_, v_minIndexable_boxed_3369_, v_showInfo_boxed_3370_, v_ext_3366_, v_ref_3367_);
return v_res_3371_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_3372_, lean_object* v_msg_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_3380_, lean_object* v_msg_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_3380_, v_msg_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_3388_, uint8_t v_attrKind_3389_, uint8_t v_showInfo_3390_, uint8_t v_minIndexable_3391_, lean_object* v_as_3392_, lean_object* v_as_x27_3393_, lean_object* v_b_3394_, lean_object* v_a_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v___x_3401_; 
v___x_3401_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3388_, v_attrKind_3389_, v_showInfo_3390_, v_minIndexable_3391_, v_as_x27_3393_, v_b_3394_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_3402_, lean_object* v_attrKind_3403_, lean_object* v_showInfo_3404_, lean_object* v_minIndexable_3405_, lean_object* v_as_3406_, lean_object* v_as_x27_3407_, lean_object* v_b_3408_, lean_object* v_a_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
uint8_t v_attrKind_boxed_3415_; uint8_t v_showInfo_boxed_3416_; uint8_t v_minIndexable_boxed_3417_; lean_object* v_res_3418_; 
v_attrKind_boxed_3415_ = lean_unbox(v_attrKind_3403_);
v_showInfo_boxed_3416_ = lean_unbox(v_showInfo_3404_);
v_minIndexable_boxed_3417_ = lean_unbox(v_minIndexable_3405_);
v_res_3418_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_3402_, v_attrKind_boxed_3415_, v_showInfo_boxed_3416_, v_minIndexable_boxed_3417_, v_as_3406_, v_as_x27_3407_, v_b_3408_, v_a_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v_as_x27_3407_);
lean_dec(v_as_3406_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object* v_00_u03b1_3419_, lean_object* v_x_3420_, uint8_t v_isExporting_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3420_, v_isExporting_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3428_, lean_object* v_x_3429_, lean_object* v_isExporting_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_){
_start:
{
uint8_t v_isExporting_boxed_3436_; lean_object* v_res_3437_; 
v_isExporting_boxed_3436_ = lean_unbox(v_isExporting_3430_);
v_res_3437_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(v_00_u03b1_3428_, v_x_3429_, v_isExporting_boxed_3436_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3431_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_3438_, lean_object* v_x_3439_, uint8_t v_when_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v___x_3446_; 
v___x_3446_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3439_, v_when_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_);
return v___x_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_3447_, lean_object* v_x_3448_, lean_object* v_when_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_){
_start:
{
uint8_t v_when_boxed_3455_; lean_object* v_res_3456_; 
v_when_boxed_3455_ = lean_unbox(v_when_3449_);
v_res_3456_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_3447_, v_x_3448_, v_when_boxed_3455_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3452_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
return v_res_3456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object* v_00_u03b2_3457_, lean_object* v_m_3458_, lean_object* v_a_3459_){
_start:
{
lean_object* v___x_3460_; 
v___x_3460_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_3458_, v_a_3459_);
return v___x_3460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3461_, lean_object* v_m_3462_, lean_object* v_a_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(v_00_u03b2_3461_, v_m_3462_, v_a_3463_);
lean_dec(v_a_3463_);
lean_dec_ref(v_m_3462_);
return v_res_3464_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3465_, lean_object* v_x_3466_, lean_object* v_x_3467_){
_start:
{
uint8_t v___x_3468_; 
v___x_3468_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_3466_, v_x_3467_);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3469_, lean_object* v_x_3470_, lean_object* v_x_3471_){
_start:
{
uint8_t v_res_3472_; lean_object* v_r_3473_; 
v_res_3472_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(v_00_u03b2_3469_, v_x_3470_, v_x_3471_);
lean_dec_ref(v_x_3471_);
lean_dec_ref(v_x_3470_);
v_r_3473_ = lean_box(v_res_3472_);
return v_r_3473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_3474_, lean_object* v_a_3475_, lean_object* v_x_3476_){
_start:
{
lean_object* v___x_3477_; 
v___x_3477_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___redArg(v_a_3475_, v_x_3476_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_3478_, lean_object* v_a_3479_, lean_object* v_x_3480_){
_start:
{
lean_object* v_res_3481_; 
v_res_3481_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__8(v_00_u03b2_3478_, v_a_3479_, v_x_3480_);
lean_dec(v_x_3480_);
lean_dec(v_a_3479_);
return v_res_3481_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3482_, lean_object* v_x_3483_, size_t v_x_3484_, lean_object* v_x_3485_){
_start:
{
uint8_t v___x_3486_; 
v___x_3486_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_3483_, v_x_3484_, v_x_3485_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3487_, lean_object* v_x_3488_, lean_object* v_x_3489_, lean_object* v_x_3490_){
_start:
{
size_t v_x_17037__boxed_3491_; uint8_t v_res_3492_; lean_object* v_r_3493_; 
v_x_17037__boxed_3491_ = lean_unbox_usize(v_x_3489_);
lean_dec(v_x_3489_);
v_res_3492_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(v_00_u03b2_3487_, v_x_3488_, v_x_17037__boxed_3491_, v_x_3490_);
lean_dec_ref(v_x_3490_);
lean_dec_ref(v_x_3488_);
v_r_3493_ = lean_box(v_res_3492_);
return v_r_3493_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(lean_object* v_00_u03b2_3494_, lean_object* v_keys_3495_, lean_object* v_vals_3496_, lean_object* v_heq_3497_, lean_object* v_i_3498_, lean_object* v_k_3499_){
_start:
{
uint8_t v___x_3500_; 
v___x_3500_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___redArg(v_keys_3495_, v_i_3498_, v_k_3499_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10___boxed(lean_object* v_00_u03b2_3501_, lean_object* v_keys_3502_, lean_object* v_vals_3503_, lean_object* v_heq_3504_, lean_object* v_i_3505_, lean_object* v_k_3506_){
_start:
{
uint8_t v_res_3507_; lean_object* v_r_3508_; 
v_res_3507_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__10(v_00_u03b2_3501_, v_keys_3502_, v_vals_3503_, v_heq_3504_, v_i_3505_, v_k_3506_);
lean_dec_ref(v_k_3506_);
lean_dec_ref(v_vals_3503_);
lean_dec_ref(v_keys_3502_);
v_r_3508_ = lean_box(v_res_3507_);
return v_r_3508_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3509_ = lean_box(0);
v___x_3510_ = lean_unsigned_to_nat(16u);
v___x_3511_ = lean_mk_array(v___x_3510_, v___x_3509_);
return v___x_3511_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3513_ = lean_unsigned_to_nat(0u);
v___x_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
lean_ctor_set(v___x_3514_, 1, v___x_3512_);
return v___x_3514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3516_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3517_ = lean_st_mk_ref(v___x_3516_);
v___x_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_3521_, lean_object* v_msg_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
lean_object* v_ref_3526_; lean_object* v___x_3527_; lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3572_; 
v_ref_3526_ = lean_ctor_get(v___y_3523_, 5);
v___x_3527_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_3522_, v___y_3523_, v___y_3524_);
v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3527_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3530_ = v___x_3527_;
v_isShared_3531_ = v_isSharedCheck_3572_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3527_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3572_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3532_; lean_object* v_traceState_3533_; lean_object* v_env_3534_; lean_object* v_nextMacroScope_3535_; lean_object* v_ngen_3536_; lean_object* v_auxDeclNGen_3537_; lean_object* v_cache_3538_; lean_object* v_messages_3539_; lean_object* v_infoState_3540_; lean_object* v_snapshotTasks_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3571_; 
v___x_3532_ = lean_st_ref_take(v___y_3524_);
v_traceState_3533_ = lean_ctor_get(v___x_3532_, 4);
v_env_3534_ = lean_ctor_get(v___x_3532_, 0);
v_nextMacroScope_3535_ = lean_ctor_get(v___x_3532_, 1);
v_ngen_3536_ = lean_ctor_get(v___x_3532_, 2);
v_auxDeclNGen_3537_ = lean_ctor_get(v___x_3532_, 3);
v_cache_3538_ = lean_ctor_get(v___x_3532_, 5);
v_messages_3539_ = lean_ctor_get(v___x_3532_, 6);
v_infoState_3540_ = lean_ctor_get(v___x_3532_, 7);
v_snapshotTasks_3541_ = lean_ctor_get(v___x_3532_, 8);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3543_ = v___x_3532_;
v_isShared_3544_ = v_isSharedCheck_3571_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_snapshotTasks_3541_);
lean_inc(v_infoState_3540_);
lean_inc(v_messages_3539_);
lean_inc(v_cache_3538_);
lean_inc(v_traceState_3533_);
lean_inc(v_auxDeclNGen_3537_);
lean_inc(v_ngen_3536_);
lean_inc(v_nextMacroScope_3535_);
lean_inc(v_env_3534_);
lean_dec(v___x_3532_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3571_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
uint64_t v_tid_3545_; lean_object* v_traces_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3570_; 
v_tid_3545_ = lean_ctor_get_uint64(v_traceState_3533_, sizeof(void*)*1);
v_traces_3546_ = lean_ctor_get(v_traceState_3533_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v_traceState_3533_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3548_ = v_traceState_3533_;
v_isShared_3549_ = v_isSharedCheck_3570_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_traces_3546_);
lean_dec(v_traceState_3533_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3570_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3550_; double v___x_3551_; uint8_t v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3560_; 
v___x_3550_ = lean_box(0);
v___x_3551_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__0);
v___x_3552_ = 0;
v___x_3553_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__1));
v___x_3554_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3554_, 0, v_cls_3521_);
lean_ctor_set(v___x_3554_, 1, v___x_3550_);
lean_ctor_set(v___x_3554_, 2, v___x_3553_);
lean_ctor_set_float(v___x_3554_, sizeof(void*)*3, v___x_3551_);
lean_ctor_set_float(v___x_3554_, sizeof(void*)*3 + 8, v___x_3551_);
lean_ctor_set_uint8(v___x_3554_, sizeof(void*)*3 + 16, v___x_3552_);
v___x_3555_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___closed__2));
v___x_3556_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3554_);
lean_ctor_set(v___x_3556_, 1, v_a_3528_);
lean_ctor_set(v___x_3556_, 2, v___x_3555_);
lean_inc(v_ref_3526_);
v___x_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3557_, 0, v_ref_3526_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = l_Lean_PersistentArray_push___redArg(v_traces_3546_, v___x_3557_);
if (v_isShared_3549_ == 0)
{
lean_ctor_set(v___x_3548_, 0, v___x_3558_);
v___x_3560_ = v___x_3548_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3558_);
lean_ctor_set_uint64(v_reuseFailAlloc_3569_, sizeof(void*)*1, v_tid_3545_);
v___x_3560_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
lean_object* v___x_3562_; 
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 4, v___x_3560_);
v___x_3562_ = v___x_3543_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_env_3534_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_nextMacroScope_3535_);
lean_ctor_set(v_reuseFailAlloc_3568_, 2, v_ngen_3536_);
lean_ctor_set(v_reuseFailAlloc_3568_, 3, v_auxDeclNGen_3537_);
lean_ctor_set(v_reuseFailAlloc_3568_, 4, v___x_3560_);
lean_ctor_set(v_reuseFailAlloc_3568_, 5, v_cache_3538_);
lean_ctor_set(v_reuseFailAlloc_3568_, 6, v_messages_3539_);
lean_ctor_set(v_reuseFailAlloc_3568_, 7, v_infoState_3540_);
lean_ctor_set(v_reuseFailAlloc_3568_, 8, v_snapshotTasks_3541_);
v___x_3562_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3566_; 
v___x_3563_ = lean_st_ref_set(v___y_3524_, v___x_3562_);
v___x_3564_ = lean_box(0);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 0, v___x_3564_);
v___x_3566_ = v___x_3530_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3564_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_3573_, lean_object* v_msg_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3573_, v_msg_3574_, v___y_3575_, v___y_3576_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_3579_, uint8_t v_isMeta_3580_, lean_object* v_hint_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v___x_3585_; lean_object* v_env_3586_; uint8_t v_isExporting_3587_; lean_object* v___x_3588_; lean_object* v_env_3589_; lean_object* v___x_3590_; lean_object* v_entry_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___y_3596_; lean_object* v___x_3621_; uint8_t v___x_3622_; 
v___x_3585_ = lean_st_ref_get(v___y_3583_);
v_env_3586_ = lean_ctor_get(v___x_3585_, 0);
lean_inc_ref(v_env_3586_);
lean_dec(v___x_3585_);
v_isExporting_3587_ = lean_ctor_get_uint8(v_env_3586_, sizeof(void*)*8);
lean_dec_ref(v_env_3586_);
v___x_3588_ = lean_st_ref_get(v___y_3583_);
v_env_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc_ref(v_env_3589_);
lean_dec(v___x_3588_);
v___x_3590_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_3579_);
v_entry_3591_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3591_, 0, v_mod_3579_);
lean_ctor_set_uint8(v_entry_3591_, sizeof(void*)*1, v_isExporting_3587_);
lean_ctor_set_uint8(v_entry_3591_, sizeof(void*)*1 + 1, v_isMeta_3580_);
v___x_3592_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3593_ = lean_box(1);
v___x_3594_ = lean_box(0);
v___x_3621_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3590_, v___x_3592_, v_env_3589_, v___x_3593_, v___x_3594_);
v___x_3622_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_3621_, v_entry_3591_);
lean_dec(v___x_3621_);
if (v___x_3622_ == 0)
{
lean_object* v_options_3623_; uint8_t v_hasTrace_3624_; 
v_options_3623_ = lean_ctor_get(v___y_3582_, 2);
v_hasTrace_3624_ = lean_ctor_get_uint8(v_options_3623_, sizeof(void*)*1);
if (v_hasTrace_3624_ == 0)
{
lean_dec(v_hint_3581_);
lean_dec(v_mod_3579_);
v___y_3596_ = v___y_3583_;
goto v___jp_3595_;
}
else
{
lean_object* v_inheritedTraceOptions_3625_; lean_object* v_cls_3626_; lean_object* v___y_3628_; lean_object* v___y_3629_; lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___x_3646_; uint8_t v___x_3647_; 
v_inheritedTraceOptions_3625_ = lean_ctor_get(v___y_3582_, 13);
v_cls_3626_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_3646_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12);
v___x_3647_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3625_, v_options_3623_, v___x_3646_);
if (v___x_3647_ == 0)
{
lean_dec(v_hint_3581_);
lean_dec(v_mod_3579_);
v___y_3596_ = v___y_3583_;
goto v___jp_3595_;
}
else
{
lean_object* v___x_3648_; lean_object* v___y_3650_; 
v___x_3648_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14);
if (v_isExporting_3587_ == 0)
{
lean_object* v___x_3657_; 
v___x_3657_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__19));
v___y_3650_ = v___x_3657_;
goto v___jp_3649_;
}
else
{
lean_object* v___x_3658_; 
v___x_3658_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__20));
v___y_3650_ = v___x_3658_;
goto v___jp_3649_;
}
v___jp_3649_:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
lean_inc_ref(v___y_3650_);
v___x_3651_ = l_Lean_stringToMessageData(v___y_3650_);
v___x_3652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3648_);
lean_ctor_set(v___x_3652_, 1, v___x_3651_);
v___x_3653_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16);
v___x_3654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3652_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
if (v_isMeta_3580_ == 0)
{
lean_object* v___x_3655_; 
v___x_3655_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_3633_ = v___x_3654_;
v___y_3634_ = v___x_3655_;
goto v___jp_3632_;
}
else
{
lean_object* v___x_3656_; 
v___x_3656_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__18));
v___y_3633_ = v___x_3654_;
v___y_3634_ = v___x_3656_;
goto v___jp_3632_;
}
}
}
v___jp_3627_:
{
lean_object* v___x_3630_; lean_object* v___x_3631_; 
v___x_3630_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___y_3628_);
lean_ctor_set(v___x_3630_, 1, v___y_3629_);
v___x_3631_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3626_, v___x_3630_, v___y_3582_, v___y_3583_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_dec_ref_known(v___x_3631_, 1);
v___y_3596_ = v___y_3583_;
goto v___jp_3595_;
}
else
{
lean_dec_ref_known(v_entry_3591_, 1);
return v___x_3631_;
}
}
v___jp_3632_:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; uint8_t v___x_3641_; 
lean_inc_ref(v___y_3634_);
v___x_3635_ = l_Lean_stringToMessageData(v___y_3634_);
v___x_3636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3636_, 0, v___y_3633_);
lean_ctor_set(v___x_3636_, 1, v___x_3635_);
v___x_3637_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_3638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3636_);
lean_ctor_set(v___x_3638_, 1, v___x_3637_);
v___x_3639_ = l_Lean_MessageData_ofName(v_mod_3579_);
v___x_3640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3638_);
lean_ctor_set(v___x_3640_, 1, v___x_3639_);
v___x_3641_ = l_Lean_Name_isAnonymous(v_hint_3581_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3642_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_3643_ = l_Lean_MessageData_ofName(v_hint_3581_);
v___x_3644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3642_);
lean_ctor_set(v___x_3644_, 1, v___x_3643_);
v___y_3628_ = v___x_3640_;
v___y_3629_ = v___x_3644_;
goto v___jp_3627_;
}
else
{
lean_object* v___x_3645_; 
lean_dec(v_hint_3581_);
v___x_3645_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_3628_ = v___x_3640_;
v___y_3629_ = v___x_3645_;
goto v___jp_3627_;
}
}
}
}
else
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
lean_dec_ref_known(v_entry_3591_, 1);
lean_dec(v_hint_3581_);
lean_dec(v_mod_3579_);
v___x_3659_ = lean_box(0);
v___x_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
return v___x_3660_;
}
v___jp_3595_:
{
lean_object* v___x_3597_; lean_object* v_toEnvExtension_3598_; lean_object* v_env_3599_; lean_object* v_nextMacroScope_3600_; lean_object* v_ngen_3601_; lean_object* v_auxDeclNGen_3602_; lean_object* v_traceState_3603_; lean_object* v_messages_3604_; lean_object* v_infoState_3605_; lean_object* v_snapshotTasks_3606_; lean_object* v___x_3608_; uint8_t v_isShared_3609_; uint8_t v_isSharedCheck_3619_; 
v___x_3597_ = lean_st_ref_take(v___y_3596_);
v_toEnvExtension_3598_ = lean_ctor_get(v___x_3592_, 0);
v_env_3599_ = lean_ctor_get(v___x_3597_, 0);
v_nextMacroScope_3600_ = lean_ctor_get(v___x_3597_, 1);
v_ngen_3601_ = lean_ctor_get(v___x_3597_, 2);
v_auxDeclNGen_3602_ = lean_ctor_get(v___x_3597_, 3);
v_traceState_3603_ = lean_ctor_get(v___x_3597_, 4);
v_messages_3604_ = lean_ctor_get(v___x_3597_, 6);
v_infoState_3605_ = lean_ctor_get(v___x_3597_, 7);
v_snapshotTasks_3606_ = lean_ctor_get(v___x_3597_, 8);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3619_ == 0)
{
lean_object* v_unused_3620_; 
v_unused_3620_ = lean_ctor_get(v___x_3597_, 5);
lean_dec(v_unused_3620_);
v___x_3608_ = v___x_3597_;
v_isShared_3609_ = v_isSharedCheck_3619_;
goto v_resetjp_3607_;
}
else
{
lean_inc(v_snapshotTasks_3606_);
lean_inc(v_infoState_3605_);
lean_inc(v_messages_3604_);
lean_inc(v_traceState_3603_);
lean_inc(v_auxDeclNGen_3602_);
lean_inc(v_ngen_3601_);
lean_inc(v_nextMacroScope_3600_);
lean_inc(v_env_3599_);
lean_dec(v___x_3597_);
v___x_3608_ = lean_box(0);
v_isShared_3609_ = v_isSharedCheck_3619_;
goto v_resetjp_3607_;
}
v_resetjp_3607_:
{
lean_object* v_asyncMode_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3614_; 
v_asyncMode_3610_ = lean_ctor_get(v_toEnvExtension_3598_, 2);
v___x_3611_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3592_, v_env_3599_, v_entry_3591_, v_asyncMode_3610_, v___x_3594_);
v___x_3612_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3609_ == 0)
{
lean_ctor_set(v___x_3608_, 5, v___x_3612_);
lean_ctor_set(v___x_3608_, 0, v___x_3611_);
v___x_3614_ = v___x_3608_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3611_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v_nextMacroScope_3600_);
lean_ctor_set(v_reuseFailAlloc_3618_, 2, v_ngen_3601_);
lean_ctor_set(v_reuseFailAlloc_3618_, 3, v_auxDeclNGen_3602_);
lean_ctor_set(v_reuseFailAlloc_3618_, 4, v_traceState_3603_);
lean_ctor_set(v_reuseFailAlloc_3618_, 5, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3618_, 6, v_messages_3604_);
lean_ctor_set(v_reuseFailAlloc_3618_, 7, v_infoState_3605_);
lean_ctor_set(v_reuseFailAlloc_3618_, 8, v_snapshotTasks_3606_);
v___x_3614_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3615_ = lean_st_ref_set(v___y_3596_, v___x_3614_);
v___x_3616_ = lean_box(0);
v___x_3617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3616_);
return v___x_3617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_3661_, lean_object* v_isMeta_3662_, lean_object* v_hint_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
uint8_t v_isMeta_boxed_3667_; lean_object* v_res_3668_; 
v_isMeta_boxed_3667_ = lean_unbox(v_isMeta_3662_);
v_res_3668_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_3661_, v_isMeta_boxed_3667_, v_hint_3663_, v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_3669_, lean_object* v_declName_3670_, lean_object* v_as_3671_, size_t v_sz_3672_, size_t v_i_3673_, lean_object* v_b_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
uint8_t v___x_3678_; 
v___x_3678_ = lean_usize_dec_lt(v_i_3673_, v_sz_3672_);
if (v___x_3678_ == 0)
{
lean_object* v___x_3679_; 
lean_dec(v_declName_3670_);
v___x_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3679_, 0, v_b_3674_);
return v___x_3679_;
}
else
{
lean_object* v___x_3680_; lean_object* v_modules_3681_; lean_object* v___x_3682_; lean_object* v_a_3683_; lean_object* v___x_3684_; lean_object* v_toImport_3685_; lean_object* v_module_3686_; uint8_t v___x_3687_; lean_object* v___x_3688_; 
v___x_3680_ = l_Lean_Environment_header(v___x_3669_);
v_modules_3681_ = lean_ctor_get(v___x_3680_, 3);
lean_inc_ref(v_modules_3681_);
lean_dec_ref(v___x_3680_);
v___x_3682_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3683_ = lean_array_uget_borrowed(v_as_3671_, v_i_3673_);
v___x_3684_ = lean_array_get(v___x_3682_, v_modules_3681_, v_a_3683_);
lean_dec_ref(v_modules_3681_);
v_toImport_3685_ = lean_ctor_get(v___x_3684_, 0);
lean_inc_ref(v_toImport_3685_);
lean_dec(v___x_3684_);
v_module_3686_ = lean_ctor_get(v_toImport_3685_, 0);
lean_inc(v_module_3686_);
lean_dec_ref(v_toImport_3685_);
v___x_3687_ = 0;
lean_inc(v_declName_3670_);
v___x_3688_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3686_, v___x_3687_, v_declName_3670_, v___y_3675_, v___y_3676_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v___x_3689_; size_t v___x_3690_; size_t v___x_3691_; 
lean_dec_ref_known(v___x_3688_, 1);
v___x_3689_ = lean_box(0);
v___x_3690_ = ((size_t)1ULL);
v___x_3691_ = lean_usize_add(v_i_3673_, v___x_3690_);
v_i_3673_ = v___x_3691_;
v_b_3674_ = v___x_3689_;
goto _start;
}
else
{
lean_dec(v_declName_3670_);
return v___x_3688_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_3693_, lean_object* v_declName_3694_, lean_object* v_as_3695_, lean_object* v_sz_3696_, lean_object* v_i_3697_, lean_object* v_b_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
size_t v_sz_boxed_3702_; size_t v_i_boxed_3703_; lean_object* v_res_3704_; 
v_sz_boxed_3702_ = lean_unbox_usize(v_sz_3696_);
lean_dec(v_sz_3696_);
v_i_boxed_3703_ = lean_unbox_usize(v_i_3697_);
lean_dec(v_i_3697_);
v_res_3704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_3693_, v_declName_3694_, v_as_3695_, v_sz_boxed_3702_, v_i_boxed_3703_, v_b_3698_, v___y_3699_, v___y_3700_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec_ref(v_as_3695_);
lean_dec_ref(v___x_3693_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_3705_, uint8_t v_isMeta_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
lean_object* v___x_3710_; lean_object* v_env_3714_; lean_object* v___y_3716_; lean_object* v___x_3729_; 
v___x_3710_ = lean_st_ref_get(v___y_3708_);
v_env_3714_ = lean_ctor_get(v___x_3710_, 0);
lean_inc_ref(v_env_3714_);
lean_dec(v___x_3710_);
v___x_3729_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3714_, v_declName_3705_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_dec_ref(v_env_3714_);
lean_dec(v_declName_3705_);
goto v___jp_3711_;
}
else
{
lean_object* v_val_3730_; lean_object* v___x_3731_; lean_object* v_modules_3732_; lean_object* v___x_3733_; uint8_t v___x_3734_; 
v_val_3730_ = lean_ctor_get(v___x_3729_, 0);
lean_inc(v_val_3730_);
lean_dec_ref_known(v___x_3729_, 1);
v___x_3731_ = l_Lean_Environment_header(v_env_3714_);
v_modules_3732_ = lean_ctor_get(v___x_3731_, 3);
lean_inc_ref(v_modules_3732_);
lean_dec_ref(v___x_3731_);
v___x_3733_ = lean_array_get_size(v_modules_3732_);
v___x_3734_ = lean_nat_dec_lt(v_val_3730_, v___x_3733_);
if (v___x_3734_ == 0)
{
lean_dec_ref(v_modules_3732_);
lean_dec(v_val_3730_);
lean_dec_ref(v_env_3714_);
lean_dec(v_declName_3705_);
goto v___jp_3711_;
}
else
{
lean_object* v___x_3735_; lean_object* v_env_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; uint8_t v___y_3740_; 
v___x_3735_ = lean_st_ref_get(v___y_3708_);
v_env_3736_ = lean_ctor_get(v___x_3735_, 0);
lean_inc_ref(v_env_3736_);
lean_dec(v___x_3735_);
v___x_3737_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3738_ = lean_array_fget(v_modules_3732_, v_val_3730_);
lean_dec(v_val_3730_);
lean_dec_ref(v_modules_3732_);
if (v_isMeta_3706_ == 0)
{
lean_dec_ref(v_env_3736_);
v___y_3740_ = v_isMeta_3706_;
goto v___jp_3739_;
}
else
{
uint8_t v___x_3751_; 
lean_inc(v_declName_3705_);
v___x_3751_ = l_Lean_isMarkedMeta(v_env_3736_, v_declName_3705_);
if (v___x_3751_ == 0)
{
v___y_3740_ = v_isMeta_3706_;
goto v___jp_3739_;
}
else
{
uint8_t v___x_3752_; 
v___x_3752_ = 0;
v___y_3740_ = v___x_3752_;
goto v___jp_3739_;
}
}
v___jp_3739_:
{
lean_object* v_toImport_3741_; lean_object* v_module_3742_; lean_object* v___x_3743_; 
v_toImport_3741_ = lean_ctor_get(v___x_3738_, 0);
lean_inc_ref(v_toImport_3741_);
lean_dec(v___x_3738_);
v_module_3742_ = lean_ctor_get(v_toImport_3741_, 0);
lean_inc(v_module_3742_);
lean_dec_ref(v_toImport_3741_);
lean_inc(v_declName_3705_);
v___x_3743_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3742_, v___y_3740_, v_declName_3705_, v___y_3707_, v___y_3708_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; 
lean_dec_ref_known(v___x_3743_, 1);
v___x_3744_ = l_Lean_indirectModUseExt;
v___x_3745_ = lean_box(1);
v___x_3746_ = lean_box(0);
lean_inc_ref(v_env_3714_);
v___x_3747_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3737_, v___x_3744_, v_env_3714_, v___x_3745_, v___x_3746_);
v___x_3748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3747_, v_declName_3705_);
lean_dec(v___x_3747_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v___x_3749_; 
v___x_3749_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_3716_ = v___x_3749_;
goto v___jp_3715_;
}
else
{
lean_object* v_val_3750_; 
v_val_3750_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_val_3750_);
lean_dec_ref_known(v___x_3748_, 1);
v___y_3716_ = v_val_3750_;
goto v___jp_3715_;
}
}
else
{
lean_dec_ref(v_env_3714_);
lean_dec(v_declName_3705_);
return v___x_3743_;
}
}
}
}
v___jp_3711_:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = lean_box(0);
v___x_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
return v___x_3713_;
}
v___jp_3715_:
{
lean_object* v___x_3717_; size_t v_sz_3718_; size_t v___x_3719_; lean_object* v___x_3720_; 
v___x_3717_ = lean_box(0);
v_sz_3718_ = lean_array_size(v___y_3716_);
v___x_3719_ = ((size_t)0ULL);
v___x_3720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_3714_, v_declName_3705_, v___y_3716_, v_sz_3718_, v___x_3719_, v___x_3717_, v___y_3707_, v___y_3708_);
lean_dec_ref(v___y_3716_);
lean_dec_ref(v_env_3714_);
if (lean_obj_tag(v___x_3720_) == 0)
{
lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3720_);
if (v_isSharedCheck_3727_ == 0)
{
lean_object* v_unused_3728_; 
v_unused_3728_ = lean_ctor_get(v___x_3720_, 0);
lean_dec(v_unused_3728_);
v___x_3722_ = v___x_3720_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_dec(v___x_3720_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v___x_3717_);
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3717_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
else
{
return v___x_3720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_3753_, lean_object* v_isMeta_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
uint8_t v_isMeta_boxed_3758_; lean_object* v_res_3759_; 
v_isMeta_boxed_3758_ = lean_unbox(v_isMeta_3754_);
v_res_3759_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_3753_, v_isMeta_boxed_3758_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_){
_start:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3764_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3765_ = lean_st_ref_get(v___x_3764_);
v___x_3766_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3765_, v_attrName_3760_);
lean_dec(v___x_3765_);
if (lean_obj_tag(v___x_3766_) == 1)
{
lean_object* v_val_3767_; lean_object* v_ext_3768_; lean_object* v_name_3769_; uint8_t v___x_3770_; lean_object* v___x_3771_; 
v_val_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_val_3767_);
v_ext_3768_ = lean_ctor_get(v_val_3767_, 1);
lean_inc_ref(v_ext_3768_);
lean_dec(v_val_3767_);
v_name_3769_ = lean_ctor_get(v_ext_3768_, 1);
lean_inc(v_name_3769_);
lean_dec_ref(v_ext_3768_);
v___x_3770_ = 1;
v___x_3771_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_3769_, v___x_3770_, v_a_3761_, v_a_3762_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v___x_3773_; uint8_t v_isShared_3774_; uint8_t v_isSharedCheck_3778_; 
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3778_ == 0)
{
lean_object* v_unused_3779_; 
v_unused_3779_ = lean_ctor_get(v___x_3771_, 0);
lean_dec(v_unused_3779_);
v___x_3773_ = v___x_3771_;
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
else
{
lean_dec(v___x_3771_);
v___x_3773_ = lean_box(0);
v_isShared_3774_ = v_isSharedCheck_3778_;
goto v_resetjp_3772_;
}
v_resetjp_3772_:
{
lean_object* v___x_3776_; 
if (v_isShared_3774_ == 0)
{
lean_ctor_set(v___x_3773_, 0, v___x_3766_);
v___x_3776_ = v___x_3773_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3766_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
else
{
lean_object* v_a_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
lean_dec_ref_known(v___x_3766_, 1);
v_a_3780_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3782_ = v___x_3771_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_inc(v_a_3780_);
lean_dec(v___x_3771_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3780_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
}
else
{
lean_object* v___x_3788_; 
v___x_3788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3766_);
return v___x_3788_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_){
_start:
{
lean_object* v_res_3793_; 
v_res_3793_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_3789_, v_a_3790_, v_a_3791_);
lean_dec(v_a_3791_);
lean_dec_ref(v_a_3790_);
lean_dec(v_attrName_3789_);
return v_res_3793_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_3795_, lean_object* v_x_3796_){
_start:
{
if (lean_obj_tag(v_x_3796_) == 0)
{
return v_x_3795_;
}
else
{
lean_object* v_key_3797_; lean_object* v_value_3798_; lean_object* v_tail_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3825_; 
v_key_3797_ = lean_ctor_get(v_x_3796_, 0);
v_value_3798_ = lean_ctor_get(v_x_3796_, 1);
v_tail_3799_ = lean_ctor_get(v_x_3796_, 2);
v_isSharedCheck_3825_ = !lean_is_exclusive(v_x_3796_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3801_ = v_x_3796_;
v_isShared_3802_ = v_isSharedCheck_3825_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_tail_3799_);
lean_inc(v_value_3798_);
lean_inc(v_key_3797_);
lean_dec(v_x_3796_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3825_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; uint64_t v___y_3805_; 
v___x_3803_ = lean_array_get_size(v_x_3795_);
if (lean_obj_tag(v_key_3797_) == 0)
{
uint64_t v___x_3823_; 
v___x_3823_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_3805_ = v___x_3823_;
goto v___jp_3804_;
}
else
{
uint64_t v_hash_3824_; 
v_hash_3824_ = lean_ctor_get_uint64(v_key_3797_, sizeof(void*)*2);
v___y_3805_ = v_hash_3824_;
goto v___jp_3804_;
}
v___jp_3804_:
{
uint64_t v___x_3806_; uint64_t v___x_3807_; uint64_t v_fold_3808_; uint64_t v___x_3809_; uint64_t v___x_3810_; uint64_t v___x_3811_; size_t v___x_3812_; size_t v___x_3813_; size_t v___x_3814_; size_t v___x_3815_; size_t v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3819_; 
v___x_3806_ = 32ULL;
v___x_3807_ = lean_uint64_shift_right(v___y_3805_, v___x_3806_);
v_fold_3808_ = lean_uint64_xor(v___y_3805_, v___x_3807_);
v___x_3809_ = 16ULL;
v___x_3810_ = lean_uint64_shift_right(v_fold_3808_, v___x_3809_);
v___x_3811_ = lean_uint64_xor(v_fold_3808_, v___x_3810_);
v___x_3812_ = lean_uint64_to_usize(v___x_3811_);
v___x_3813_ = lean_usize_of_nat(v___x_3803_);
v___x_3814_ = ((size_t)1ULL);
v___x_3815_ = lean_usize_sub(v___x_3813_, v___x_3814_);
v___x_3816_ = lean_usize_land(v___x_3812_, v___x_3815_);
v___x_3817_ = lean_array_uget_borrowed(v_x_3795_, v___x_3816_);
lean_inc(v___x_3817_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 2, v___x_3817_);
v___x_3819_ = v___x_3801_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_key_3797_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v_value_3798_);
lean_ctor_set(v_reuseFailAlloc_3822_, 2, v___x_3817_);
v___x_3819_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
lean_object* v___x_3820_; 
v___x_3820_ = lean_array_uset(v_x_3795_, v___x_3816_, v___x_3819_);
v_x_3795_ = v___x_3820_;
v_x_3796_ = v_tail_3799_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3826_, lean_object* v_source_3827_, lean_object* v_target_3828_){
_start:
{
lean_object* v___x_3829_; uint8_t v___x_3830_; 
v___x_3829_ = lean_array_get_size(v_source_3827_);
v___x_3830_ = lean_nat_dec_lt(v_i_3826_, v___x_3829_);
if (v___x_3830_ == 0)
{
lean_dec_ref(v_source_3827_);
lean_dec(v_i_3826_);
return v_target_3828_;
}
else
{
lean_object* v_es_3831_; lean_object* v___x_3832_; lean_object* v_source_3833_; lean_object* v_target_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v_es_3831_ = lean_array_fget(v_source_3827_, v_i_3826_);
v___x_3832_ = lean_box(0);
v_source_3833_ = lean_array_fset(v_source_3827_, v_i_3826_, v___x_3832_);
v_target_3834_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3828_, v_es_3831_);
v___x_3835_ = lean_unsigned_to_nat(1u);
v___x_3836_ = lean_nat_add(v_i_3826_, v___x_3835_);
lean_dec(v_i_3826_);
v_i_3826_ = v___x_3836_;
v_source_3827_ = v_source_3833_;
v_target_3828_ = v_target_3834_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_3838_){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v_nbuckets_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; 
v___x_3839_ = lean_array_get_size(v_data_3838_);
v___x_3840_ = lean_unsigned_to_nat(2u);
v_nbuckets_3841_ = lean_nat_mul(v___x_3839_, v___x_3840_);
v___x_3842_ = lean_unsigned_to_nat(0u);
v___x_3843_ = lean_box(0);
v___x_3844_ = lean_mk_array(v_nbuckets_3841_, v___x_3843_);
v___x_3845_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_3842_, v_data_3838_, v___x_3844_);
return v___x_3845_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_3846_, lean_object* v_x_3847_){
_start:
{
if (lean_obj_tag(v_x_3847_) == 0)
{
uint8_t v___x_3848_; 
v___x_3848_ = 0;
return v___x_3848_;
}
else
{
lean_object* v_key_3849_; lean_object* v_tail_3850_; uint8_t v___x_3851_; 
v_key_3849_ = lean_ctor_get(v_x_3847_, 0);
v_tail_3850_ = lean_ctor_get(v_x_3847_, 2);
v___x_3851_ = lean_name_eq(v_key_3849_, v_a_3846_);
if (v___x_3851_ == 0)
{
v_x_3847_ = v_tail_3850_;
goto _start;
}
else
{
return v___x_3851_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_3853_, lean_object* v_x_3854_){
_start:
{
uint8_t v_res_3855_; lean_object* v_r_3856_; 
v_res_3855_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3853_, v_x_3854_);
lean_dec(v_x_3854_);
lean_dec(v_a_3853_);
v_r_3856_ = lean_box(v_res_3855_);
return v_r_3856_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_3857_, lean_object* v_b_3858_, lean_object* v_x_3859_){
_start:
{
if (lean_obj_tag(v_x_3859_) == 0)
{
lean_dec(v_b_3858_);
lean_dec(v_a_3857_);
return v_x_3859_;
}
else
{
lean_object* v_key_3860_; lean_object* v_value_3861_; lean_object* v_tail_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3874_; 
v_key_3860_ = lean_ctor_get(v_x_3859_, 0);
v_value_3861_ = lean_ctor_get(v_x_3859_, 1);
v_tail_3862_ = lean_ctor_get(v_x_3859_, 2);
v_isSharedCheck_3874_ = !lean_is_exclusive(v_x_3859_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3864_ = v_x_3859_;
v_isShared_3865_ = v_isSharedCheck_3874_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_tail_3862_);
lean_inc(v_value_3861_);
lean_inc(v_key_3860_);
lean_dec(v_x_3859_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3874_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
uint8_t v___x_3866_; 
v___x_3866_ = lean_name_eq(v_key_3860_, v_a_3857_);
if (v___x_3866_ == 0)
{
lean_object* v___x_3867_; lean_object* v___x_3869_; 
v___x_3867_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3857_, v_b_3858_, v_tail_3862_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 2, v___x_3867_);
v___x_3869_ = v___x_3864_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_key_3860_);
lean_ctor_set(v_reuseFailAlloc_3870_, 1, v_value_3861_);
lean_ctor_set(v_reuseFailAlloc_3870_, 2, v___x_3867_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
else
{
lean_object* v___x_3872_; 
lean_dec(v_value_3861_);
lean_dec(v_key_3860_);
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 1, v_b_3858_);
lean_ctor_set(v___x_3864_, 0, v_a_3857_);
v___x_3872_ = v___x_3864_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3857_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v_b_3858_);
lean_ctor_set(v_reuseFailAlloc_3873_, 2, v_tail_3862_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_3875_, lean_object* v_a_3876_, lean_object* v_b_3877_){
_start:
{
lean_object* v_size_3878_; lean_object* v_buckets_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3925_; 
v_size_3878_ = lean_ctor_get(v_m_3875_, 0);
v_buckets_3879_ = lean_ctor_get(v_m_3875_, 1);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_m_3875_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3881_ = v_m_3875_;
v_isShared_3882_ = v_isSharedCheck_3925_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_buckets_3879_);
lean_inc(v_size_3878_);
lean_dec(v_m_3875_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3925_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3883_; uint64_t v___y_3885_; 
v___x_3883_ = lean_array_get_size(v_buckets_3879_);
if (lean_obj_tag(v_a_3876_) == 0)
{
uint64_t v___x_3923_; 
v___x_3923_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_3885_ = v___x_3923_;
goto v___jp_3884_;
}
else
{
uint64_t v_hash_3924_; 
v_hash_3924_ = lean_ctor_get_uint64(v_a_3876_, sizeof(void*)*2);
v___y_3885_ = v_hash_3924_;
goto v___jp_3884_;
}
v___jp_3884_:
{
uint64_t v___x_3886_; uint64_t v___x_3887_; uint64_t v_fold_3888_; uint64_t v___x_3889_; uint64_t v___x_3890_; uint64_t v___x_3891_; size_t v___x_3892_; size_t v___x_3893_; size_t v___x_3894_; size_t v___x_3895_; size_t v___x_3896_; lean_object* v_bkt_3897_; uint8_t v___x_3898_; 
v___x_3886_ = 32ULL;
v___x_3887_ = lean_uint64_shift_right(v___y_3885_, v___x_3886_);
v_fold_3888_ = lean_uint64_xor(v___y_3885_, v___x_3887_);
v___x_3889_ = 16ULL;
v___x_3890_ = lean_uint64_shift_right(v_fold_3888_, v___x_3889_);
v___x_3891_ = lean_uint64_xor(v_fold_3888_, v___x_3890_);
v___x_3892_ = lean_uint64_to_usize(v___x_3891_);
v___x_3893_ = lean_usize_of_nat(v___x_3883_);
v___x_3894_ = ((size_t)1ULL);
v___x_3895_ = lean_usize_sub(v___x_3893_, v___x_3894_);
v___x_3896_ = lean_usize_land(v___x_3892_, v___x_3895_);
v_bkt_3897_ = lean_array_uget_borrowed(v_buckets_3879_, v___x_3896_);
v___x_3898_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3876_, v_bkt_3897_);
if (v___x_3898_ == 0)
{
lean_object* v___x_3899_; lean_object* v_size_x27_3900_; lean_object* v___x_3901_; lean_object* v_buckets_x27_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; uint8_t v___x_3908_; 
v___x_3899_ = lean_unsigned_to_nat(1u);
v_size_x27_3900_ = lean_nat_add(v_size_3878_, v___x_3899_);
lean_dec(v_size_3878_);
lean_inc(v_bkt_3897_);
v___x_3901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3901_, 0, v_a_3876_);
lean_ctor_set(v___x_3901_, 1, v_b_3877_);
lean_ctor_set(v___x_3901_, 2, v_bkt_3897_);
v_buckets_x27_3902_ = lean_array_uset(v_buckets_3879_, v___x_3896_, v___x_3901_);
v___x_3903_ = lean_unsigned_to_nat(4u);
v___x_3904_ = lean_nat_mul(v_size_x27_3900_, v___x_3903_);
v___x_3905_ = lean_unsigned_to_nat(3u);
v___x_3906_ = lean_nat_div(v___x_3904_, v___x_3905_);
lean_dec(v___x_3904_);
v___x_3907_ = lean_array_get_size(v_buckets_x27_3902_);
v___x_3908_ = lean_nat_dec_le(v___x_3906_, v___x_3907_);
lean_dec(v___x_3906_);
if (v___x_3908_ == 0)
{
lean_object* v_val_3909_; lean_object* v___x_3911_; 
v_val_3909_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_3902_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 1, v_val_3909_);
lean_ctor_set(v___x_3881_, 0, v_size_x27_3900_);
v___x_3911_ = v___x_3881_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_size_x27_3900_);
lean_ctor_set(v_reuseFailAlloc_3912_, 1, v_val_3909_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
else
{
lean_object* v___x_3914_; 
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 1, v_buckets_x27_3902_);
lean_ctor_set(v___x_3881_, 0, v_size_x27_3900_);
v___x_3914_ = v___x_3881_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_size_x27_3900_);
lean_ctor_set(v_reuseFailAlloc_3915_, 1, v_buckets_x27_3902_);
v___x_3914_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
return v___x_3914_;
}
}
}
else
{
lean_object* v___x_3916_; lean_object* v_buckets_x27_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3921_; 
lean_inc(v_bkt_3897_);
v___x_3916_ = lean_box(0);
v_buckets_x27_3917_ = lean_array_uset(v_buckets_3879_, v___x_3896_, v___x_3916_);
v___x_3918_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3876_, v_b_3877_, v_bkt_3897_);
v___x_3919_ = lean_array_uset(v_buckets_x27_3917_, v___x_3896_, v___x_3918_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 1, v___x_3919_);
v___x_3921_ = v___x_3881_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_size_3878_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_3926_, lean_object* v_ref_3927_){
_start:
{
lean_object* v___x_3929_; 
lean_inc(v_ref_3927_);
v___x_3929_ = l_Lean_Meta_Grind_mkExtension(v_ref_3927_);
if (lean_obj_tag(v___x_3929_) == 0)
{
lean_object* v_a_3930_; uint8_t v___x_3931_; uint8_t v___x_3932_; lean_object* v___x_3933_; 
v_a_3930_ = lean_ctor_get(v___x_3929_, 0);
lean_inc_n(v_a_3930_, 2);
lean_dec_ref_known(v___x_3929_, 1);
v___x_3931_ = 0;
v___x_3932_ = 1;
lean_inc(v_ref_3927_);
lean_inc(v_attrName_3926_);
v___x_3933_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3926_, v___x_3931_, v___x_3932_, v_a_3930_, v_ref_3927_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v___x_3934_; 
lean_dec_ref_known(v___x_3933_, 1);
lean_inc(v_ref_3927_);
lean_inc(v_a_3930_);
lean_inc(v_attrName_3926_);
v___x_3934_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3926_, v___x_3931_, v___x_3931_, v_a_3930_, v_ref_3927_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v___x_3935_; 
lean_dec_ref_known(v___x_3934_, 1);
lean_inc(v_ref_3927_);
lean_inc(v_a_3930_);
lean_inc(v_attrName_3926_);
v___x_3935_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3926_, v___x_3932_, v___x_3932_, v_a_3930_, v_ref_3927_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v___x_3936_; 
lean_dec_ref_known(v___x_3935_, 1);
lean_inc(v_a_3930_);
lean_inc(v_attrName_3926_);
v___x_3936_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3926_, v___x_3932_, v___x_3931_, v_a_3930_, v_ref_3927_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3947_; 
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3947_ == 0)
{
lean_object* v_unused_3948_; 
v_unused_3948_ = lean_ctor_get(v___x_3936_, 0);
lean_dec(v_unused_3948_);
v___x_3938_ = v___x_3936_;
v_isShared_3939_ = v_isSharedCheck_3947_;
goto v_resetjp_3937_;
}
else
{
lean_dec(v___x_3936_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3947_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3945_; 
v___x_3940_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3941_ = lean_st_ref_take(v___x_3940_);
lean_inc(v_a_3930_);
v___x_3942_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_3941_, v_attrName_3926_, v_a_3930_);
v___x_3943_ = lean_st_ref_set(v___x_3940_, v___x_3942_);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v_a_3930_);
v___x_3945_ = v___x_3938_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3930_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
else
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
lean_dec(v_a_3930_);
lean_dec(v_attrName_3926_);
v_a_3949_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3936_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3936_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec(v_a_3930_);
lean_dec(v_ref_3927_);
lean_dec(v_attrName_3926_);
v_a_3957_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3935_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3935_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_dec(v_a_3930_);
lean_dec(v_ref_3927_);
lean_dec(v_attrName_3926_);
v_a_3965_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3934_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3934_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec(v_a_3930_);
lean_dec(v_ref_3927_);
lean_dec(v_attrName_3926_);
v_a_3973_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3933_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3933_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
else
{
lean_dec(v_ref_3927_);
lean_dec(v_attrName_3926_);
return v___x_3929_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_3981_, lean_object* v_ref_3982_, lean_object* v_a_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_Lean_Meta_Grind_registerAttr(v_attrName_3981_, v_ref_3982_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_3985_, lean_object* v_m_3986_, lean_object* v_a_3987_, lean_object* v_b_3988_){
_start:
{
lean_object* v___x_3989_; 
v___x_3989_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_3986_, v_a_3987_, v_b_3988_);
return v___x_3989_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_3990_, lean_object* v_a_3991_, lean_object* v_x_3992_){
_start:
{
uint8_t v___x_3993_; 
v___x_3993_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3991_, v_x_3992_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_3994_, lean_object* v_a_3995_, lean_object* v_x_3996_){
_start:
{
uint8_t v_res_3997_; lean_object* v_r_3998_; 
v_res_3997_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_3994_, v_a_3995_, v_x_3996_);
lean_dec(v_x_3996_);
lean_dec(v_a_3995_);
v_r_3998_ = lean_box(v_res_3997_);
return v_r_3998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_3999_, lean_object* v_data_4000_){
_start:
{
lean_object* v___x_4001_; 
v___x_4001_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_4000_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_4002_, lean_object* v_a_4003_, lean_object* v_b_4004_, lean_object* v_x_4005_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4003_, v_b_4004_, v_x_4005_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4007_, lean_object* v_i_4008_, lean_object* v_source_4009_, lean_object* v_target_4010_){
_start:
{
lean_object* v___x_4011_; 
v___x_4011_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_4008_, v_source_4009_, v_target_4010_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4012_, lean_object* v_x_4013_, lean_object* v_x_4014_){
_start:
{
lean_object* v___x_4015_; 
v___x_4015_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_4013_, v_x_4014_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4022_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_4023_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_4024_ = l_Lean_Meta_Grind_registerAttr(v___x_4022_, v___x_4023_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4037_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4038_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_));
v___x_4039_ = l_Lean_Meta_Grind_registerAttr(v___x_4037_, v___x_4038_);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2____boxed(lean_object* v_a_4040_){
_start:
{
lean_object* v_res_4041_; 
v_res_4041_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
return v_res_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_4042_, lean_object* v_a_4043_){
_start:
{
lean_object* v___x_4045_; lean_object* v_env_4046_; lean_object* v___x_4047_; lean_object* v_ext_4048_; lean_object* v_toEnvExtension_4049_; lean_object* v_asyncMode_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v_casesTypes_4053_; uint8_t v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4045_ = lean_st_ref_get(v_a_4043_);
v_env_4046_ = lean_ctor_get(v___x_4045_, 0);
lean_inc_ref(v_env_4046_);
lean_dec(v___x_4045_);
v___x_4047_ = l_Lean_Meta_Grind_grindExt;
v_ext_4048_ = lean_ctor_get(v___x_4047_, 1);
v_toEnvExtension_4049_ = lean_ctor_get(v_ext_4048_, 0);
v_asyncMode_4050_ = lean_ctor_get(v_toEnvExtension_4049_, 2);
v___x_4051_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4052_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4051_, v___x_4047_, v_env_4046_, v_asyncMode_4050_);
v_casesTypes_4053_ = lean_ctor_get(v___x_4052_, 0);
lean_inc_ref(v_casesTypes_4053_);
lean_dec(v___x_4052_);
v___x_4054_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_4053_, v_declName_4042_);
lean_dec_ref(v_casesTypes_4053_);
v___x_4055_ = lean_box(v___x_4054_);
v___x_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_){
_start:
{
lean_object* v_res_4060_; 
v_res_4060_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4057_, v_a_4058_);
lean_dec(v_a_4058_);
lean_dec(v_declName_4057_);
return v_res_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_4061_, lean_object* v_a_4062_, lean_object* v_a_4063_){
_start:
{
lean_object* v___x_4065_; 
v___x_4065_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4061_, v_a_4063_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_){
_start:
{
lean_object* v_res_4070_; 
v_res_4070_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_4066_, v_a_4067_, v_a_4068_);
lean_dec(v_a_4068_);
lean_dec_ref(v_a_4067_);
lean_dec(v_declName_4066_);
return v_res_4070_;
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
res = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_4077740362____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_liaExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_liaExt);
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
