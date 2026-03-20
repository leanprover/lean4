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
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
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
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "normExt"};
static const lean_object* l_Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l_Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__3_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(1, 117, 24, 11, 244, 218, 170, 88)}};
static const lean_object* l_Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__8_value),LEAN_SCALAR_PTR_LITERAL(179, 34, 219, 24, 240, 38, 65, 204)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindDef"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__10_value),LEAN_SCALAR_PTR_LITERAL(66, 218, 12, 28, 39, 29, 4, 77)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindFwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__12_value),LEAN_SCALAR_PTR_LITERAL(121, 161, 177, 116, 112, 162, 92, 47)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__13_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__14_value),LEAN_SCALAR_PTR_LITERAL(114, 163, 57, 243, 160, 41, 114, 23)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqRhs"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__16_value),LEAN_SCALAR_PTR_LITERAL(222, 187, 148, 221, 105, 213, 199, 68)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__17_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindEqBoth"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__18_value),LEAN_SCALAR_PTR_LITERAL(79, 230, 133, 190, 186, 228, 109, 128)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__19_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindEqBwd"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__20_value),LEAN_SCALAR_PTR_LITERAL(250, 57, 23, 180, 238, 116, 90, 53)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__21 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__21_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindLR"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__22_value),LEAN_SCALAR_PTR_LITERAL(152, 111, 188, 78, 132, 212, 97, 164)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__23_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "grindRL"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__24 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__24_value),LEAN_SCALAR_PTR_LITERAL(84, 112, 237, 169, 105, 148, 42, 205)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__25 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__25_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindUsr"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__26 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__26_value),LEAN_SCALAR_PTR_LITERAL(204, 58, 160, 148, 192, 167, 114, 18)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__27 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__27_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindGen"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__28 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__28_value),LEAN_SCALAR_PTR_LITERAL(186, 203, 120, 147, 97, 215, 208, 134)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__29 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__29_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindCases"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__30 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__30_value),LEAN_SCALAR_PTR_LITERAL(85, 142, 28, 230, 49, 50, 229, 162)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__31 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__31_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "grindCasesEager"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__32 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__32_value),LEAN_SCALAR_PTR_LITERAL(75, 210, 92, 40, 190, 183, 142, 70)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__33 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__33_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindIntro"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__34 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__34_value),LEAN_SCALAR_PTR_LITERAL(142, 126, 114, 89, 237, 253, 56, 138)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__35 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__35_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindExt"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__36 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value),LEAN_SCALAR_PTR_LITERAL(147, 193, 153, 166, 243, 149, 163, 253)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__37 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__37_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindInj"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__38 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__38_value),LEAN_SCALAR_PTR_LITERAL(223, 225, 41, 9, 21, 5, 145, 193)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__39 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__39_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "grindFunCC"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__40 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__40_value),LEAN_SCALAR_PTR_LITERAL(217, 20, 186, 134, 249, 79, 78, 43)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__41 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__41_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "grindNorm"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__42 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__42_value),LEAN_SCALAR_PTR_LITERAL(166, 126, 146, 239, 104, 253, 29, 148)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__43 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__43_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "grindUnfold"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__44 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__44_value),LEAN_SCALAR_PTR_LITERAL(214, 181, 37, 92, 122, 232, 164, 219)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__45 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__45_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "grindSym"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__46 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__46_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__51_value),LEAN_SCALAR_PTR_LITERAL(38, 218, 35, 149, 208, 200, 230, 161)}};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__52 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__52_value;
static const lean_string_object l_Lean_Meta_Grind_getAttrKindCore___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "simpPre"};
static const lean_object* l_Lean_Meta_Grind_getAttrKindCore___closed__53 = (const lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__53_value;
static const lean_ctor_object l_Lean_Meta_Grind_getAttrKindCore___closed__54_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__50_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__1_value;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2;
static const lean_array_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 115, .m_capacity = 115, .m_length = 114, .m_data = "\?]` is a helper attribute for displaying inferred patterns, if you want to remove the attribute, consider using `["};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "]` instead"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12;
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__9___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__9___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__9(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_extensionMapRef;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Meta_Grind_initFn___closed__2_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 56, 216, 97, 9, 85, 52, 211)}};
static const lean_ctor_object l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Meta_Grind_getAttrKindCore___closed__36_value),LEAN_SCALAR_PTR_LITERAL(160, 1, 171, 211, 177, 132, 129, 49)}};
static const lean_object* l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_grindExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = ((lean_object*)(l_Lean_Meta_Grind_initFn___closed__4_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_));
v___x_12_ = l_Lean_Meta_mkSimpExt(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2____boxed(lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
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
v___x_139_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v___x_138_);
lean_ctor_set(v___x_139_, 2, v___x_138_);
lean_ctor_set(v___x_139_, 3, v___x_137_);
lean_ctor_set(v___x_139_, 4, v___x_137_);
lean_ctor_set(v___x_139_, 5, v___x_137_);
lean_ctor_set(v___x_139_, 6, v___x_137_);
lean_ctor_set(v___x_139_, 7, v___x_137_);
lean_ctor_set(v___x_139_, 8, v___x_137_);
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
lean_object* v_fileName_195_; lean_object* v_fileMap_196_; lean_object* v_options_197_; lean_object* v_currRecDepth_198_; lean_object* v_maxRecDepth_199_; lean_object* v_ref_200_; lean_object* v_currNamespace_201_; lean_object* v_openDecls_202_; lean_object* v_initHeartbeats_203_; lean_object* v_maxHeartbeats_204_; lean_object* v_quotContext_205_; lean_object* v_currMacroScope_206_; uint8_t v_diag_207_; lean_object* v_cancelTk_x3f_208_; uint8_t v_suppressElabErrors_209_; lean_object* v_inheritedTraceOptions_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_219_; 
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
v_isSharedCheck_219_ = !lean_is_exclusive(v___y_192_);
if (v_isSharedCheck_219_ == 0)
{
v___x_212_ = v___y_192_;
v_isShared_213_ = v_isSharedCheck_219_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_inheritedTraceOptions_210_);
lean_inc(v_cancelTk_x3f_208_);
lean_inc(v_currMacroScope_206_);
lean_inc(v_quotContext_205_);
lean_inc(v_maxHeartbeats_204_);
lean_inc(v_initHeartbeats_203_);
lean_inc(v_openDecls_202_);
lean_inc(v_currNamespace_201_);
lean_inc(v_ref_200_);
lean_inc(v_maxRecDepth_199_);
lean_inc(v_currRecDepth_198_);
lean_inc(v_options_197_);
lean_inc(v_fileMap_196_);
lean_inc(v_fileName_195_);
lean_dec(v___y_192_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_219_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_ref_214_; lean_object* v___x_216_; 
v_ref_214_ = l_Lean_replaceRef(v_ref_190_, v_ref_200_);
lean_dec(v_ref_200_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 5, v_ref_214_);
v___x_216_ = v___x_212_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_fileName_195_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v_fileMap_196_);
lean_ctor_set(v_reuseFailAlloc_218_, 2, v_options_197_);
lean_ctor_set(v_reuseFailAlloc_218_, 3, v_currRecDepth_198_);
lean_ctor_set(v_reuseFailAlloc_218_, 4, v_maxRecDepth_199_);
lean_ctor_set(v_reuseFailAlloc_218_, 5, v_ref_214_);
lean_ctor_set(v_reuseFailAlloc_218_, 6, v_currNamespace_201_);
lean_ctor_set(v_reuseFailAlloc_218_, 7, v_openDecls_202_);
lean_ctor_set(v_reuseFailAlloc_218_, 8, v_initHeartbeats_203_);
lean_ctor_set(v_reuseFailAlloc_218_, 9, v_maxHeartbeats_204_);
lean_ctor_set(v_reuseFailAlloc_218_, 10, v_quotContext_205_);
lean_ctor_set(v_reuseFailAlloc_218_, 11, v_currMacroScope_206_);
lean_ctor_set(v_reuseFailAlloc_218_, 12, v_cancelTk_x3f_208_);
lean_ctor_set(v_reuseFailAlloc_218_, 13, v_inheritedTraceOptions_210_);
lean_ctor_set_uint8(v_reuseFailAlloc_218_, sizeof(void*)*14, v_diag_207_);
lean_ctor_set_uint8(v_reuseFailAlloc_218_, sizeof(void*)*14 + 1, v_suppressElabErrors_209_);
v___x_216_ = v_reuseFailAlloc_218_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_191_, v___x_216_, v___y_193_);
lean_dec_ref(v___x_216_);
return v___x_217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg___boxed(lean_object* v_ref_220_, lean_object* v_msg_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_220_, v_msg_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec(v_ref_220_);
return v_res_225_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5(void){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__4));
v___x_236_ = l_Lean_stringToMessageData(v___x_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7(void){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__6));
v___x_239_ = l_Lean_stringToMessageData(v___x_238_);
return v___x_239_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_getAttrKindCore___closed__49(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__48));
v___x_362_ = l_Lean_stringToMessageData(v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore(lean_object* v_stx_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__3));
lean_inc(v_stx_390_);
v___x_395_ = l_Lean_Syntax_isOfKind(v_stx_390_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_396_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_397_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_396_);
lean_ctor_set(v___x_398_, 1, v___x_397_);
v___x_399_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_400_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_401_;
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = l_Lean_Syntax_getArg(v_stx_390_, v___x_402_);
v___x_404_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__9));
lean_inc(v___x_403_);
v___x_405_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__11));
lean_inc(v___x_403_);
v___x_407_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__13));
lean_inc(v___x_403_);
v___x_409_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_408_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__15));
lean_inc(v___x_403_);
v___x_411_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__17));
lean_inc(v___x_403_);
v___x_413_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_412_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__19));
lean_inc(v___x_403_);
v___x_415_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__21));
lean_inc(v___x_403_);
v___x_417_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__23));
lean_inc(v___x_403_);
v___x_419_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_418_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__25));
lean_inc(v___x_403_);
v___x_421_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; uint8_t v___x_423_; 
v___x_422_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__27));
lean_inc(v___x_403_);
v___x_423_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
lean_inc(v___x_403_);
v___x_425_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__31));
lean_inc(v___x_403_);
v___x_427_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__33));
lean_inc(v___x_403_);
v___x_429_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__35));
lean_inc(v___x_403_);
v___x_431_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__37));
lean_inc(v___x_403_);
v___x_433_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_434_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__39));
lean_inc(v___x_403_);
v___x_435_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__41));
lean_inc(v___x_403_);
v___x_437_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_438_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__43));
lean_inc(v___x_403_);
v___x_439_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_440_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__45));
lean_inc(v___x_403_);
v___x_441_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_440_);
if (v___x_441_ == 0)
{
lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_442_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__47));
lean_inc(v___x_403_);
v___x_443_ = l_Lean_Syntax_isOfKind(v___x_403_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec(v___x_403_);
v___x_444_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_445_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
v___x_447_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
lean_ctor_set(v___x_448_, 1, v___x_447_);
v___x_449_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_448_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec(v_stx_390_);
v___x_450_ = lean_unsigned_to_nat(1u);
v___x_451_ = l_Lean_Syntax_getArg(v___x_403_, v___x_450_);
lean_dec(v___x_403_);
v___x_452_ = l_Lean_Syntax_isNatLit_x3f(v___x_451_);
if (lean_obj_tag(v___x_452_) == 1)
{
lean_object* v_val_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_461_; 
lean_dec(v___x_451_);
lean_dec_ref(v_a_391_);
v_val_453_ = lean_ctor_get(v___x_452_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_452_);
if (v_isSharedCheck_461_ == 0)
{
v___x_455_ = v___x_452_;
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_val_453_);
lean_dec(v___x_452_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_461_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set_tag(v___x_455_, 5);
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_val_453_);
v___x_458_ = v_reuseFailAlloc_460_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; 
v___x_459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
return v___x_459_;
}
}
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec(v___x_452_);
v___x_462_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__49, &l_Lean_Meta_Grind_getAttrKindCore___closed__49_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__49);
v___x_463_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v___x_451_, v___x_462_, v_a_391_, v_a_392_);
lean_dec(v___x_451_);
return v___x_463_;
}
}
}
else
{
lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec(v___x_403_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_464_ = lean_box(9);
v___x_465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
return v___x_465_;
}
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = l_Lean_Syntax_getArg(v___x_403_, v___x_466_);
lean_inc(v___x_467_);
v___x_468_ = l_Lean_Syntax_matchesNull(v___x_467_, v___x_402_);
if (v___x_468_ == 0)
{
uint8_t v___x_469_; 
lean_inc(v___x_467_);
v___x_469_ = l_Lean_Syntax_matchesNull(v___x_467_, v___x_466_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
lean_dec(v___x_467_);
lean_dec(v___x_403_);
v___x_470_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_471_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_470_);
lean_ctor_set(v___x_472_, 1, v___x_471_);
v___x_473_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_472_);
lean_ctor_set(v___x_474_, 1, v___x_473_);
v___x_475_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_474_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_475_;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_476_ = l_Lean_Syntax_getArg(v___x_467_, v___x_402_);
lean_dec(v___x_467_);
v___x_477_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__52));
lean_inc(v___x_476_);
v___x_478_ = l_Lean_Syntax_isOfKind(v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__54));
v___x_480_ = l_Lean_Syntax_isOfKind(v___x_476_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v___x_403_);
v___x_481_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_482_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_481_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
v___x_484_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_485_, 0, v___x_483_);
lean_ctor_set(v___x_485_, 1, v___x_484_);
v___x_486_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_485_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_486_;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_487_ = lean_unsigned_to_nat(2u);
v___x_488_ = l_Lean_Syntax_getArg(v___x_403_, v___x_487_);
lean_dec(v___x_403_);
lean_inc(v___x_488_);
v___x_489_ = l_Lean_Syntax_matchesNull(v___x_488_, v___x_402_);
if (v___x_489_ == 0)
{
uint8_t v___x_490_; 
v___x_490_ = l_Lean_Syntax_matchesNull(v___x_488_, v___x_466_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_491_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_492_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_491_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
v___x_494_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_493_);
lean_ctor_set(v___x_495_, 1, v___x_494_);
v___x_496_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_495_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_496_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; 
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_497_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_497_, 0, v___x_489_);
lean_ctor_set_uint8(v___x_497_, 1, v___x_395_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_dec(v___x_488_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_499_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_499_, 0, v___x_478_);
lean_ctor_set_uint8(v___x_499_, 1, v___x_478_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
return v___x_500_;
}
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
lean_dec(v___x_476_);
v___x_501_ = lean_unsigned_to_nat(2u);
v___x_502_ = l_Lean_Syntax_getArg(v___x_403_, v___x_501_);
lean_dec(v___x_403_);
lean_inc(v___x_502_);
v___x_503_ = l_Lean_Syntax_matchesNull(v___x_502_, v___x_402_);
if (v___x_503_ == 0)
{
uint8_t v___x_504_; 
v___x_504_ = l_Lean_Syntax_matchesNull(v___x_502_, v___x_466_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_505_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_506_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_505_);
lean_ctor_set(v___x_507_, 1, v___x_506_);
v___x_508_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_509_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_509_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_510_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_511_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_511_, 0, v___x_395_);
lean_ctor_set_uint8(v___x_511_, 1, v___x_395_);
v___x_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
return v___x_512_;
}
}
else
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v___x_502_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_513_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_513_, 0, v___x_395_);
lean_ctor_set_uint8(v___x_513_, 1, v___x_468_);
v___x_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
return v___x_514_;
}
}
}
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
lean_dec(v___x_467_);
v___x_515_ = lean_unsigned_to_nat(2u);
v___x_516_ = l_Lean_Syntax_getArg(v___x_403_, v___x_515_);
lean_dec(v___x_403_);
lean_inc(v___x_516_);
v___x_517_ = l_Lean_Syntax_matchesNull(v___x_516_, v___x_402_);
if (v___x_517_ == 0)
{
uint8_t v___x_518_; 
v___x_518_ = l_Lean_Syntax_matchesNull(v___x_516_, v___x_466_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_519_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_520_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_519_);
lean_ctor_set(v___x_521_, 1, v___x_520_);
v___x_522_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_521_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_523_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_524_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; 
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_525_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_525_, 0, v___x_395_);
lean_ctor_set_uint8(v___x_525_, 1, v___x_395_);
v___x_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_526_, 0, v___x_525_);
return v___x_526_;
}
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v___x_516_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_527_ = lean_alloc_ctor(8, 0, 2);
lean_ctor_set_uint8(v___x_527_, 0, v___x_395_);
lean_ctor_set_uint8(v___x_527_, 1, v___x_437_);
v___x_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
return v___x_528_;
}
}
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v___x_403_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_529_ = lean_box(7);
v___x_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
return v___x_530_;
}
}
else
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v___x_403_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_531_ = lean_box(6);
v___x_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
return v___x_532_;
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; 
lean_dec(v___x_403_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_533_ = lean_box(4);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v___x_403_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_535_ = lean_box(2);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
else
{
lean_object* v___x_537_; lean_object* v___x_538_; 
lean_dec(v___x_403_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_537_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_537_, 0, v___x_395_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
else
{
lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec(v___x_403_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_539_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_539_, 0, v___x_425_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
lean_dec(v___x_403_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_541_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_541_, 0, v___x_395_);
v___x_542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_542_, 0, v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; 
lean_dec(v___x_403_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_544_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__55));
v___x_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
return v___x_545_;
}
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; 
lean_dec(v___x_403_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_546_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__56));
v___x_547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
return v___x_547_;
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; 
lean_dec(v___x_403_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_548_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__57));
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
else
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec(v___x_403_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_550_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__58));
v___x_551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
return v___x_551_;
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_552_ = lean_unsigned_to_nat(3u);
v___x_553_ = l_Lean_Syntax_getArg(v___x_403_, v___x_552_);
lean_dec(v___x_403_);
lean_inc(v___x_553_);
v___x_554_ = l_Lean_Syntax_matchesNull(v___x_553_, v___x_402_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_555_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_553_);
v___x_556_ = l_Lean_Syntax_matchesNull(v___x_553_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_dec(v___x_553_);
v___x_557_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_558_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
v___x_562_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_561_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_562_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_563_ = l_Lean_Syntax_getArg(v___x_553_, v___x_402_);
lean_dec(v___x_553_);
v___x_564_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_565_ = l_Lean_Syntax_isOfKind(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_566_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_567_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_566_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_570_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_571_;
}
else
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_572_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_572_, 0, v___x_395_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
v___x_574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_574_, 0, v___x_573_);
return v___x_574_;
}
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v___x_553_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_575_ = lean_alloc_ctor(2, 0, 1);
lean_ctor_set_uint8(v___x_575_, 0, v___x_413_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
}
else
{
lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_578_ = lean_unsigned_to_nat(2u);
v___x_579_ = l_Lean_Syntax_getArg(v___x_403_, v___x_578_);
lean_dec(v___x_403_);
lean_inc(v___x_579_);
v___x_580_ = l_Lean_Syntax_matchesNull(v___x_579_, v___x_402_);
if (v___x_580_ == 0)
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_579_);
v___x_582_ = l_Lean_Syntax_matchesNull(v___x_579_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v___x_579_);
v___x_583_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_584_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_587_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v___x_589_ = l_Lean_Syntax_getArg(v___x_579_, v___x_402_);
lean_dec(v___x_579_);
v___x_590_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_591_ = l_Lean_Syntax_isOfKind(v___x_589_, v___x_590_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_592_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_593_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_594_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_594_, 0, v___x_592_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_594_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
v___x_597_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_596_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_597_;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_598_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_598_, 0, v___x_395_);
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v___x_599_);
return v___x_600_;
}
}
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v___x_579_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_601_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_601_, 0, v___x_411_);
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = l_Lean_Syntax_getArg(v___x_403_, v___x_604_);
lean_dec(v___x_403_);
lean_inc(v___x_605_);
v___x_606_ = l_Lean_Syntax_matchesNull(v___x_605_, v___x_402_);
if (v___x_606_ == 0)
{
uint8_t v___x_607_; 
lean_inc(v___x_605_);
v___x_607_ = l_Lean_Syntax_matchesNull(v___x_605_, v___x_604_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec(v___x_605_);
v___x_608_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_609_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_612_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_613_;
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_614_ = l_Lean_Syntax_getArg(v___x_605_, v___x_402_);
lean_dec(v___x_605_);
v___x_615_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_616_ = l_Lean_Syntax_isOfKind(v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_617_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_618_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_619_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_621_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_622_;
}
else
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_623_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_623_, 0, v___x_395_);
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v___x_623_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
}
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
lean_dec(v___x_605_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_626_ = lean_alloc_ctor(5, 0, 1);
lean_ctor_set_uint8(v___x_626_, 0, v___x_409_);
v___x_627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec(v___x_403_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_629_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__59));
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = l_Lean_Syntax_getArg(v___x_403_, v___x_631_);
lean_dec(v___x_403_);
lean_inc(v___x_632_);
v___x_633_ = l_Lean_Syntax_matchesNull(v___x_632_, v___x_402_);
if (v___x_633_ == 0)
{
uint8_t v___x_634_; 
lean_inc(v___x_632_);
v___x_634_ = l_Lean_Syntax_matchesNull(v___x_632_, v___x_631_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
lean_dec(v___x_632_);
v___x_635_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_636_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_635_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
v___x_638_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_639_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_640_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_641_ = l_Lean_Syntax_getArg(v___x_632_, v___x_402_);
lean_dec(v___x_632_);
v___x_642_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_643_ = l_Lean_Syntax_isOfKind(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_644_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_645_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_648_, 0, v___x_646_);
lean_ctor_set(v___x_648_, 1, v___x_647_);
v___x_649_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_648_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_650_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_650_, 0, v___x_395_);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
v___x_652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
return v___x_652_;
}
}
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec(v___x_632_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_653_ = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(v___x_653_, 0, v___x_405_);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = l_Lean_Syntax_getArg(v___x_403_, v___x_656_);
lean_dec(v___x_403_);
lean_inc(v___x_657_);
v___x_658_ = l_Lean_Syntax_matchesNull(v___x_657_, v___x_402_);
if (v___x_658_ == 0)
{
uint8_t v___x_659_; 
lean_inc(v___x_657_);
v___x_659_ = l_Lean_Syntax_matchesNull(v___x_657_, v___x_656_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
lean_dec(v___x_657_);
v___x_660_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_661_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_660_);
lean_ctor_set(v___x_662_, 1, v___x_661_);
v___x_663_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v___x_665_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_664_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_665_;
}
else
{
lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_666_ = l_Lean_Syntax_getArg(v___x_657_, v___x_402_);
lean_dec(v___x_657_);
v___x_667_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__29));
v___x_668_ = l_Lean_Syntax_isOfKind(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_669_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__5, &l_Lean_Meta_Grind_getAttrKindCore___closed__5_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__5);
v___x_670_ = l_Lean_MessageData_ofSyntax(v_stx_390_);
v___x_671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_669_);
lean_ctor_set(v___x_671_, 1, v___x_670_);
v___x_672_ = lean_obj_once(&l_Lean_Meta_Grind_getAttrKindCore___closed__7, &l_Lean_Meta_Grind_getAttrKindCore___closed__7_once, _init_l_Lean_Meta_Grind_getAttrKindCore___closed__7);
v___x_673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_673_, v_a_391_, v_a_392_);
lean_dec_ref(v_a_391_);
return v___x_674_;
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_675_ = lean_alloc_ctor(0, 0, 1);
lean_ctor_set_uint8(v___x_675_, 0, v___x_395_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
return v___x_677_;
}
}
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; 
lean_dec(v___x_657_);
lean_dec_ref(v_a_391_);
lean_dec(v_stx_390_);
v___x_678_ = ((lean_object*)(l_Lean_Meta_Grind_getAttrKindCore___closed__61));
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v___x_678_);
return v___x_679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindCore___boxed(lean_object* v_stx_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_Meta_Grind_getAttrKindCore(v_stx_680_, v_a_681_, v_a_682_);
lean_dec(v_a_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(lean_object* v_00_u03b1_685_, lean_object* v_msg_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
lean_object* v___x_690_; 
v___x_690_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v_msg_686_, v___y_687_, v___y_688_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___boxed(lean_object* v_00_u03b1_691_, lean_object* v_msg_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0(v_00_u03b1_691_, v_msg_692_, v___y_693_, v___y_694_);
lean_dec(v___y_694_);
lean_dec_ref(v___y_693_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(lean_object* v_00_u03b1_697_, lean_object* v_ref_698_, lean_object* v_msg_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___redArg(v_ref_698_, v_msg_699_, v___y_700_, v___y_701_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1___boxed(lean_object* v_00_u03b1_704_, lean_object* v_ref_705_, lean_object* v_msg_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_throwErrorAt___at___00Lean_Meta_Grind_getAttrKindCore_spec__1(v_00_u03b1_704_, v_ref_705_, v_msg_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec(v_ref_705_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt(lean_object* v_stx_711_, lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_715_ = lean_unsigned_to_nat(1u);
v___x_716_ = l_Lean_Syntax_getArg(v_stx_711_, v___x_715_);
v___x_717_ = l_Lean_Syntax_isNone(v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = l_Lean_Syntax_getArg(v___x_716_, v___x_718_);
lean_dec(v___x_716_);
v___x_720_ = l_Lean_Meta_Grind_getAttrKindCore(v___x_719_, v_a_712_, v_a_713_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; 
lean_dec(v___x_716_);
lean_dec_ref(v_a_712_);
v___x_721_ = lean_box(3);
v___x_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getAttrKindFromOpt___boxed(lean_object* v_stx_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_723_, v_a_724_, v_a_725_);
lean_dec(v_a_725_);
lean_dec(v_stx_723_);
return v_res_727_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = ((lean_object*)(l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__0));
v___x_730_ = l_Lean_stringToMessageData(v___x_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_obj_once(&l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1, &l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1_once, _init_l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___closed__1);
v___x_735_ = l_Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0___redArg(v___x_734_, v_a_731_, v_a_732_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg___boxed(lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_736_, v_a_737_);
lean_dec(v_a_737_);
lean_dec_ref(v_a_736_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier(lean_object* v_00_u03b1_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v_a_741_, v_a_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_throwInvalidUsrModifier___boxed(lean_object* v_00_u03b1_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_Lean_Meta_Grind_throwInvalidUsrModifier(v_00_u03b1_745_, v_a_746_, v_a_747_);
lean_dec(v_a_747_);
lean_dec_ref(v_a_746_);
return v_res_749_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_750_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__0);
v___x_752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(lean_object* v_ext_755_, lean_object* v_b_756_, uint8_t v_kind_757_, lean_object* v___y_758_, lean_object* v___y_759_){
_start:
{
lean_object* v_currNamespace_761_; lean_object* v___x_762_; lean_object* v_env_763_; lean_object* v_nextMacroScope_764_; lean_object* v_ngen_765_; lean_object* v_auxDeclNGen_766_; lean_object* v_traceState_767_; lean_object* v_messages_768_; lean_object* v_infoState_769_; lean_object* v_snapshotTasks_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_782_; 
v_currNamespace_761_ = lean_ctor_get(v___y_758_, 6);
lean_inc(v_currNamespace_761_);
lean_dec_ref(v___y_758_);
v___x_762_ = lean_st_ref_take(v___y_759_);
v_env_763_ = lean_ctor_get(v___x_762_, 0);
v_nextMacroScope_764_ = lean_ctor_get(v___x_762_, 1);
v_ngen_765_ = lean_ctor_get(v___x_762_, 2);
v_auxDeclNGen_766_ = lean_ctor_get(v___x_762_, 3);
v_traceState_767_ = lean_ctor_get(v___x_762_, 4);
v_messages_768_ = lean_ctor_get(v___x_762_, 6);
v_infoState_769_ = lean_ctor_get(v___x_762_, 7);
v_snapshotTasks_770_ = lean_ctor_get(v___x_762_, 8);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v___x_762_, 5);
lean_dec(v_unused_783_);
v___x_772_ = v___x_762_;
v_isShared_773_ = v_isSharedCheck_782_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_snapshotTasks_770_);
lean_inc(v_infoState_769_);
lean_inc(v_messages_768_);
lean_inc(v_traceState_767_);
lean_inc(v_auxDeclNGen_766_);
lean_inc(v_ngen_765_);
lean_inc(v_nextMacroScope_764_);
lean_inc(v_env_763_);
lean_dec(v___x_762_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_782_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_774_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_763_, v_ext_755_, v_b_756_, v_kind_757_, v_currNamespace_761_);
v___x_775_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 5, v___x_775_);
lean_ctor_set(v___x_772_, 0, v___x_774_);
v___x_777_ = v___x_772_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_nextMacroScope_764_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_ngen_765_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v_auxDeclNGen_766_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v_traceState_767_);
lean_ctor_set(v_reuseFailAlloc_781_, 5, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_781_, 6, v_messages_768_);
lean_ctor_set(v_reuseFailAlloc_781_, 7, v_infoState_769_);
lean_ctor_set(v_reuseFailAlloc_781_, 8, v_snapshotTasks_770_);
v___x_777_ = v_reuseFailAlloc_781_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = lean_st_ref_set(v___y_759_, v___x_777_);
v___x_779_ = lean_box(0);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
return v___x_780_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___boxed(lean_object* v_ext_784_, lean_object* v_b_785_, lean_object* v_kind_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_){
_start:
{
uint8_t v_kind_boxed_790_; lean_object* v_res_791_; 
v_kind_boxed_790_ = lean_unbox(v_kind_786_);
v_res_791_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_784_, v_b_785_, v_kind_boxed_790_, v___y_787_, v___y_788_);
lean_dec(v___y_788_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(lean_object* v_00_u03b1_792_, lean_object* v_00_u03b2_793_, lean_object* v_00_u03c3_794_, lean_object* v_ext_795_, lean_object* v_b_796_, uint8_t v_kind_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_795_, v_b_796_, v_kind_797_, v___y_798_, v___y_799_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___boxed(lean_object* v_00_u03b1_802_, lean_object* v_00_u03b2_803_, lean_object* v_00_u03c3_804_, lean_object* v_ext_805_, lean_object* v_b_806_, lean_object* v_kind_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
uint8_t v_kind_boxed_811_; lean_object* v_res_812_; 
v_kind_boxed_811_ = lean_unbox(v_kind_807_);
v_res_812_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0(v_00_u03b1_802_, v_00_u03b2_803_, v_00_u03c3_804_, v_ext_805_, v_b_806_, v_kind_boxed_811_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(lean_object* v_ext_813_, lean_object* v_declName_814_, uint8_t v_eager_815_, uint8_t v_attrKind_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___x_820_; 
lean_inc(v_declName_814_);
v___x_820_ = l_Lean_Meta_Grind_validateCasesAttr(v_declName_814_, v_eager_815_, v_a_817_, v_a_818_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec_ref(v___x_820_);
v___x_821_ = lean_alloc_ctor(2, 1, 1);
lean_ctor_set(v___x_821_, 0, v_declName_814_);
lean_ctor_set_uint8(v___x_821_, sizeof(void*)*1, v_eager_815_);
v___x_822_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_813_, v___x_821_, v_attrKind_816_, v_a_817_, v_a_818_);
return v___x_822_;
}
else
{
lean_dec_ref(v_a_817_);
lean_dec(v_declName_814_);
lean_dec_ref(v_ext_813_);
return v___x_820_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr___boxed(lean_object* v_ext_823_, lean_object* v_declName_824_, lean_object* v_eager_825_, lean_object* v_attrKind_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
uint8_t v_eager_boxed_830_; uint8_t v_attrKind_boxed_831_; lean_object* v_res_832_; 
v_eager_boxed_830_ = lean_unbox(v_eager_825_);
v_attrKind_boxed_831_ = lean_unbox(v_attrKind_826_);
v_res_832_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_823_, v_declName_824_, v_eager_boxed_830_, v_attrKind_boxed_831_, v_a_827_, v_a_828_);
lean_dec(v_a_828_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(lean_object* v_ext_833_, lean_object* v_declName_834_, uint8_t v_attrKind_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v___x_839_; 
lean_inc(v_declName_834_);
v___x_839_ = l_Lean_Meta_Grind_validateExtAttr(v_declName_834_, v_a_836_, v_a_837_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_847_; 
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; 
v_unused_848_ = lean_ctor_get(v___x_839_, 0);
lean_dec(v_unused_848_);
v___x_841_ = v___x_839_;
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
else
{
lean_dec(v___x_839_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v_declName_834_);
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_declName_834_);
v___x_844_ = v_reuseFailAlloc_846_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; 
v___x_845_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_833_, v___x_844_, v_attrKind_835_, v_a_836_, v_a_837_);
return v___x_845_;
}
}
}
else
{
lean_dec_ref(v_a_836_);
lean_dec(v_declName_834_);
lean_dec_ref(v_ext_833_);
return v___x_839_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr___boxed(lean_object* v_ext_849_, lean_object* v_declName_850_, lean_object* v_attrKind_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
uint8_t v_attrKind_boxed_855_; lean_object* v_res_856_; 
v_attrKind_boxed_855_ = lean_unbox(v_attrKind_851_);
v_res_856_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_849_, v_declName_850_, v_attrKind_boxed_855_, v_a_852_, v_a_853_);
lean_dec(v_a_853_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(lean_object* v_ext_857_, lean_object* v_declName_858_, uint8_t v_attrKind_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_863_, 0, v_declName_858_);
v___x_864_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg(v_ext_857_, v___x_863_, v_attrKind_859_, v_a_860_, v_a_861_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr___boxed(lean_object* v_ext_865_, lean_object* v_declName_866_, lean_object* v_attrKind_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
uint8_t v_attrKind_boxed_871_; lean_object* v_res_872_; 
v_attrKind_boxed_871_ = lean_unbox(v_attrKind_867_);
v_res_872_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_865_, v_declName_866_, v_attrKind_boxed_871_, v_a_868_, v_a_869_);
lean_dec(v_a_869_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0(lean_object* v_a_873_, lean_object* v_s_874_){
_start:
{
lean_object* v_casesTypes_875_; lean_object* v_funCC_876_; lean_object* v_ematch_877_; lean_object* v_inj_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
v_casesTypes_875_ = lean_ctor_get(v_s_874_, 0);
v_funCC_876_ = lean_ctor_get(v_s_874_, 2);
v_ematch_877_ = lean_ctor_get(v_s_874_, 3);
v_inj_878_ = lean_ctor_get(v_s_874_, 4);
v_isSharedCheck_885_ = !lean_is_exclusive(v_s_874_);
if (v_isSharedCheck_885_ == 0)
{
lean_object* v_unused_886_; 
v_unused_886_ = lean_ctor_get(v_s_874_, 1);
lean_dec(v_unused_886_);
v___x_880_ = v_s_874_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_inj_878_);
lean_inc(v_ematch_877_);
lean_inc(v_funCC_876_);
lean_inc(v_casesTypes_875_);
lean_dec(v_s_874_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 1, v_a_873_);
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_casesTypes_875_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_a_873_);
lean_ctor_set(v_reuseFailAlloc_884_, 2, v_funCC_876_);
lean_ctor_set(v_reuseFailAlloc_884_, 3, v_ematch_877_);
lean_ctor_set(v_reuseFailAlloc_884_, 4, v_inj_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(lean_object* v_ext_887_, lean_object* v_declName_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___x_892_; lean_object* v_ext_893_; lean_object* v_toEnvExtension_894_; lean_object* v_env_895_; lean_object* v_asyncMode_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v_extThms_899_; lean_object* v___x_900_; 
v___x_892_ = lean_st_ref_get(v_a_890_);
v_ext_893_ = lean_ctor_get(v_ext_887_, 1);
v_toEnvExtension_894_ = lean_ctor_get(v_ext_893_, 0);
v_env_895_ = lean_ctor_get(v___x_892_, 0);
lean_inc_ref(v_env_895_);
lean_dec(v___x_892_);
v_asyncMode_896_ = lean_ctor_get(v_toEnvExtension_894_, 2);
v___x_897_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_898_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_897_, v_ext_887_, v_env_895_, v_asyncMode_896_);
v_extThms_899_ = lean_ctor_get(v___x_898_, 1);
lean_inc_ref(v_extThms_899_);
lean_dec(v___x_898_);
v___x_900_ = l_Lean_Meta_Grind_ExtTheorems_eraseDecl(v_extThms_899_, v_declName_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v___x_903_; uint8_t v_isShared_904_; uint8_t v_isSharedCheck_930_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_930_ == 0)
{
v___x_903_ = v___x_900_;
v_isShared_904_ = v_isSharedCheck_930_;
goto v_resetjp_902_;
}
else
{
lean_inc(v_a_901_);
lean_dec(v___x_900_);
v___x_903_ = lean_box(0);
v_isShared_904_ = v_isSharedCheck_930_;
goto v_resetjp_902_;
}
v_resetjp_902_:
{
lean_object* v___x_905_; lean_object* v_env_906_; lean_object* v_nextMacroScope_907_; lean_object* v_ngen_908_; lean_object* v_auxDeclNGen_909_; lean_object* v_traceState_910_; lean_object* v_messages_911_; lean_object* v_infoState_912_; lean_object* v_snapshotTasks_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_928_; 
v___x_905_ = lean_st_ref_take(v_a_890_);
v_env_906_ = lean_ctor_get(v___x_905_, 0);
v_nextMacroScope_907_ = lean_ctor_get(v___x_905_, 1);
v_ngen_908_ = lean_ctor_get(v___x_905_, 2);
v_auxDeclNGen_909_ = lean_ctor_get(v___x_905_, 3);
v_traceState_910_ = lean_ctor_get(v___x_905_, 4);
v_messages_911_ = lean_ctor_get(v___x_905_, 6);
v_infoState_912_ = lean_ctor_get(v___x_905_, 7);
v_snapshotTasks_913_ = lean_ctor_get(v___x_905_, 8);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v___x_905_, 5);
lean_dec(v_unused_929_);
v___x_915_ = v___x_905_;
v_isShared_916_ = v_isSharedCheck_928_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_snapshotTasks_913_);
lean_inc(v_infoState_912_);
lean_inc(v_messages_911_);
lean_inc(v_traceState_910_);
lean_inc(v_auxDeclNGen_909_);
lean_inc(v_ngen_908_);
lean_inc(v_nextMacroScope_907_);
lean_inc(v_env_906_);
lean_dec(v___x_905_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_928_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___f_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_921_; 
v___f_917_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___lam__0), 2, 1);
lean_closure_set(v___f_917_, 0, v_a_901_);
v___x_918_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_887_, v_env_906_, v___f_917_);
v___x_919_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 5, v___x_919_);
lean_ctor_set(v___x_915_, 0, v___x_918_);
v___x_921_ = v___x_915_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_927_, 1, v_nextMacroScope_907_);
lean_ctor_set(v_reuseFailAlloc_927_, 2, v_ngen_908_);
lean_ctor_set(v_reuseFailAlloc_927_, 3, v_auxDeclNGen_909_);
lean_ctor_set(v_reuseFailAlloc_927_, 4, v_traceState_910_);
lean_ctor_set(v_reuseFailAlloc_927_, 5, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_927_, 6, v_messages_911_);
lean_ctor_set(v_reuseFailAlloc_927_, 7, v_infoState_912_);
lean_ctor_set(v_reuseFailAlloc_927_, 8, v_snapshotTasks_913_);
v___x_921_ = v_reuseFailAlloc_927_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_925_; 
v___x_922_ = lean_st_ref_set(v_a_890_, v___x_921_);
v___x_923_ = lean_box(0);
if (v_isShared_904_ == 0)
{
lean_ctor_set(v___x_903_, 0, v___x_923_);
v___x_925_ = v___x_903_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec_ref(v_ext_887_);
v_a_931_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_900_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_900_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr___boxed(lean_object* v_ext_939_, lean_object* v_declName_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_939_, v_declName_940_, v_a_941_, v_a_942_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0(lean_object* v_a_945_, lean_object* v_s_946_){
_start:
{
lean_object* v_extThms_947_; lean_object* v_funCC_948_; lean_object* v_ematch_949_; lean_object* v_inj_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
v_extThms_947_ = lean_ctor_get(v_s_946_, 1);
v_funCC_948_ = lean_ctor_get(v_s_946_, 2);
v_ematch_949_ = lean_ctor_get(v_s_946_, 3);
v_inj_950_ = lean_ctor_get(v_s_946_, 4);
v_isSharedCheck_957_ = !lean_is_exclusive(v_s_946_);
if (v_isSharedCheck_957_ == 0)
{
lean_object* v_unused_958_; 
v_unused_958_ = lean_ctor_get(v_s_946_, 0);
lean_dec(v_unused_958_);
v___x_952_ = v_s_946_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_inj_950_);
lean_inc(v_ematch_949_);
lean_inc(v_funCC_948_);
lean_inc(v_extThms_947_);
lean_dec(v_s_946_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_955_; 
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v_a_945_);
v___x_955_ = v___x_952_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_945_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_extThms_947_);
lean_ctor_set(v_reuseFailAlloc_956_, 2, v_funCC_948_);
lean_ctor_set(v_reuseFailAlloc_956_, 3, v_ematch_949_);
lean_ctor_set(v_reuseFailAlloc_956_, 4, v_inj_950_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(lean_object* v_ext_959_, lean_object* v_declName_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v___x_964_; 
lean_inc(v_declName_960_);
v___x_964_ = l_Lean_Meta_Grind_ensureNotBuiltinCases(v_declName_960_, v_a_961_, v_a_962_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v___x_965_; lean_object* v_ext_966_; lean_object* v_toEnvExtension_967_; lean_object* v_env_968_; lean_object* v_asyncMode_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v_casesTypes_972_; lean_object* v___x_973_; 
lean_dec_ref(v___x_964_);
v___x_965_ = lean_st_ref_get(v_a_962_);
v_ext_966_ = lean_ctor_get(v_ext_959_, 1);
v_toEnvExtension_967_ = lean_ctor_get(v_ext_966_, 0);
v_env_968_ = lean_ctor_get(v___x_965_, 0);
lean_inc_ref(v_env_968_);
lean_dec(v___x_965_);
v_asyncMode_969_ = lean_ctor_get(v_toEnvExtension_967_, 2);
v___x_970_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_971_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_970_, v_ext_959_, v_env_968_, v_asyncMode_969_);
v_casesTypes_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc_ref(v_casesTypes_972_);
lean_dec(v___x_971_);
v___x_973_ = l_Lean_Meta_Grind_CasesTypes_eraseDecl(v_casesTypes_972_, v_declName_960_, v_a_961_, v_a_962_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_1003_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_1003_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_1003_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v_env_979_; lean_object* v_nextMacroScope_980_; lean_object* v_ngen_981_; lean_object* v_auxDeclNGen_982_; lean_object* v_traceState_983_; lean_object* v_messages_984_; lean_object* v_infoState_985_; lean_object* v_snapshotTasks_986_; lean_object* v___x_988_; uint8_t v_isShared_989_; uint8_t v_isSharedCheck_1001_; 
v___x_978_ = lean_st_ref_take(v_a_962_);
v_env_979_ = lean_ctor_get(v___x_978_, 0);
v_nextMacroScope_980_ = lean_ctor_get(v___x_978_, 1);
v_ngen_981_ = lean_ctor_get(v___x_978_, 2);
v_auxDeclNGen_982_ = lean_ctor_get(v___x_978_, 3);
v_traceState_983_ = lean_ctor_get(v___x_978_, 4);
v_messages_984_ = lean_ctor_get(v___x_978_, 6);
v_infoState_985_ = lean_ctor_get(v___x_978_, 7);
v_snapshotTasks_986_ = lean_ctor_get(v___x_978_, 8);
v_isSharedCheck_1001_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1001_ == 0)
{
lean_object* v_unused_1002_; 
v_unused_1002_ = lean_ctor_get(v___x_978_, 5);
lean_dec(v_unused_1002_);
v___x_988_ = v___x_978_;
v_isShared_989_ = v_isSharedCheck_1001_;
goto v_resetjp_987_;
}
else
{
lean_inc(v_snapshotTasks_986_);
lean_inc(v_infoState_985_);
lean_inc(v_messages_984_);
lean_inc(v_traceState_983_);
lean_inc(v_auxDeclNGen_982_);
lean_inc(v_ngen_981_);
lean_inc(v_nextMacroScope_980_);
lean_inc(v_env_979_);
lean_dec(v___x_978_);
v___x_988_ = lean_box(0);
v_isShared_989_ = v_isSharedCheck_1001_;
goto v_resetjp_987_;
}
v_resetjp_987_:
{
lean_object* v___f_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_994_; 
v___f_990_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___lam__0), 2, 1);
lean_closure_set(v___f_990_, 0, v_a_974_);
v___x_991_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_959_, v_env_979_, v___f_990_);
v___x_992_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_989_ == 0)
{
lean_ctor_set(v___x_988_, 5, v___x_992_);
lean_ctor_set(v___x_988_, 0, v___x_991_);
v___x_994_ = v___x_988_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_1000_; 
v_reuseFailAlloc_1000_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1000_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_1000_, 1, v_nextMacroScope_980_);
lean_ctor_set(v_reuseFailAlloc_1000_, 2, v_ngen_981_);
lean_ctor_set(v_reuseFailAlloc_1000_, 3, v_auxDeclNGen_982_);
lean_ctor_set(v_reuseFailAlloc_1000_, 4, v_traceState_983_);
lean_ctor_set(v_reuseFailAlloc_1000_, 5, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_1000_, 6, v_messages_984_);
lean_ctor_set(v_reuseFailAlloc_1000_, 7, v_infoState_985_);
lean_ctor_set(v_reuseFailAlloc_1000_, 8, v_snapshotTasks_986_);
v___x_994_ = v_reuseFailAlloc_1000_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_995_ = lean_st_ref_set(v_a_962_, v___x_994_);
v___x_996_ = lean_box(0);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_996_);
v___x_998_ = v___x_976_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_996_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
}
else
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1011_; 
lean_dec_ref(v_ext_959_);
v_a_1004_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_1006_ = v___x_973_;
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_973_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1011_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1009_; 
if (v_isShared_1007_ == 0)
{
v___x_1009_ = v___x_1006_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_a_1004_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
else
{
lean_dec(v_declName_960_);
lean_dec_ref(v_ext_959_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr___boxed(lean_object* v_ext_1012_, lean_object* v_declName_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_1012_, v_declName_1013_, v_a_1014_, v_a_1015_);
lean_dec(v_a_1015_);
lean_dec_ref(v_a_1014_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0(lean_object* v___x_1018_, lean_object* v_s_1019_){
_start:
{
lean_object* v_casesTypes_1020_; lean_object* v_extThms_1021_; lean_object* v_ematch_1022_; lean_object* v_inj_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
v_casesTypes_1020_ = lean_ctor_get(v_s_1019_, 0);
v_extThms_1021_ = lean_ctor_get(v_s_1019_, 1);
v_ematch_1022_ = lean_ctor_get(v_s_1019_, 3);
v_inj_1023_ = lean_ctor_get(v_s_1019_, 4);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_s_1019_);
if (v_isSharedCheck_1030_ == 0)
{
lean_object* v_unused_1031_; 
v_unused_1031_ = lean_ctor_get(v_s_1019_, 2);
lean_dec(v_unused_1031_);
v___x_1025_ = v_s_1019_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_inj_1023_);
lean_inc(v_ematch_1022_);
lean_inc(v_extThms_1021_);
lean_inc(v_casesTypes_1020_);
lean_dec(v_s_1019_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
lean_ctor_set(v___x_1025_, 2, v___x_1018_);
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_casesTypes_1020_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_extThms_1021_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1029_, 3, v_ematch_1022_);
lean_ctor_set(v_reuseFailAlloc_1029_, 4, v_inj_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(lean_object* v_k_1032_, lean_object* v_t_1033_){
_start:
{
if (lean_obj_tag(v_t_1033_) == 0)
{
lean_object* v_k_1034_; lean_object* v_v_1035_; lean_object* v_l_1036_; lean_object* v_r_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1691_; 
v_k_1034_ = lean_ctor_get(v_t_1033_, 1);
v_v_1035_ = lean_ctor_get(v_t_1033_, 2);
v_l_1036_ = lean_ctor_get(v_t_1033_, 3);
v_r_1037_ = lean_ctor_get(v_t_1033_, 4);
v_isSharedCheck_1691_ = !lean_is_exclusive(v_t_1033_);
if (v_isSharedCheck_1691_ == 0)
{
lean_object* v_unused_1692_; 
v_unused_1692_ = lean_ctor_get(v_t_1033_, 0);
lean_dec(v_unused_1692_);
v___x_1039_ = v_t_1033_;
v_isShared_1040_ = v_isSharedCheck_1691_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_r_1037_);
lean_inc(v_l_1036_);
lean_inc(v_v_1035_);
lean_inc(v_k_1034_);
lean_dec(v_t_1033_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1691_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
uint8_t v___x_1041_; 
v___x_1041_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1032_, v_k_1034_);
switch(v___x_1041_)
{
case 0:
{
lean_object* v_impl_1042_; lean_object* v___x_1043_; 
v_impl_1042_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1032_, v_l_1036_);
v___x_1043_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1042_) == 0)
{
if (lean_obj_tag(v_r_1037_) == 0)
{
lean_object* v_size_1044_; lean_object* v_size_1045_; lean_object* v_k_1046_; lean_object* v_v_1047_; lean_object* v_l_1048_; lean_object* v_r_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v_size_1044_ = lean_ctor_get(v_impl_1042_, 0);
lean_inc(v_size_1044_);
v_size_1045_ = lean_ctor_get(v_r_1037_, 0);
v_k_1046_ = lean_ctor_get(v_r_1037_, 1);
v_v_1047_ = lean_ctor_get(v_r_1037_, 2);
v_l_1048_ = lean_ctor_get(v_r_1037_, 3);
lean_inc(v_l_1048_);
v_r_1049_ = lean_ctor_get(v_r_1037_, 4);
v___x_1050_ = lean_unsigned_to_nat(3u);
v___x_1051_ = lean_nat_mul(v___x_1050_, v_size_1044_);
v___x_1052_ = lean_nat_dec_lt(v___x_1051_, v_size_1045_);
lean_dec(v___x_1051_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
lean_dec(v_l_1048_);
v___x_1053_ = lean_nat_add(v___x_1043_, v_size_1044_);
lean_dec(v_size_1044_);
v___x_1054_ = lean_nat_add(v___x_1053_, v_size_1045_);
lean_dec(v___x_1053_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 3, v_impl_1042_);
lean_ctor_set(v___x_1039_, 0, v___x_1054_);
v___x_1056_ = v___x_1039_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1057_, 3, v_impl_1042_);
lean_ctor_set(v_reuseFailAlloc_1057_, 4, v_r_1037_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
else
{
lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1121_; 
lean_inc(v_r_1049_);
lean_inc(v_v_1047_);
lean_inc(v_k_1046_);
lean_inc(v_size_1045_);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_r_1037_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; lean_object* v_unused_1123_; lean_object* v_unused_1124_; lean_object* v_unused_1125_; lean_object* v_unused_1126_; 
v_unused_1122_ = lean_ctor_get(v_r_1037_, 4);
lean_dec(v_unused_1122_);
v_unused_1123_ = lean_ctor_get(v_r_1037_, 3);
lean_dec(v_unused_1123_);
v_unused_1124_ = lean_ctor_get(v_r_1037_, 2);
lean_dec(v_unused_1124_);
v_unused_1125_ = lean_ctor_get(v_r_1037_, 1);
lean_dec(v_unused_1125_);
v_unused_1126_ = lean_ctor_get(v_r_1037_, 0);
lean_dec(v_unused_1126_);
v___x_1059_ = v_r_1037_;
v_isShared_1060_ = v_isSharedCheck_1121_;
goto v_resetjp_1058_;
}
else
{
lean_dec(v_r_1037_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1121_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v_size_1061_; lean_object* v_k_1062_; lean_object* v_v_1063_; lean_object* v_l_1064_; lean_object* v_r_1065_; lean_object* v_size_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v_size_1061_ = lean_ctor_get(v_l_1048_, 0);
v_k_1062_ = lean_ctor_get(v_l_1048_, 1);
v_v_1063_ = lean_ctor_get(v_l_1048_, 2);
v_l_1064_ = lean_ctor_get(v_l_1048_, 3);
v_r_1065_ = lean_ctor_get(v_l_1048_, 4);
v_size_1066_ = lean_ctor_get(v_r_1049_, 0);
v___x_1067_ = lean_unsigned_to_nat(2u);
v___x_1068_ = lean_nat_mul(v___x_1067_, v_size_1066_);
v___x_1069_ = lean_nat_dec_lt(v_size_1061_, v___x_1068_);
lean_dec(v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1097_; 
lean_inc(v_r_1065_);
lean_inc(v_l_1064_);
lean_inc(v_v_1063_);
lean_inc(v_k_1062_);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_l_1048_);
if (v_isSharedCheck_1097_ == 0)
{
lean_object* v_unused_1098_; lean_object* v_unused_1099_; lean_object* v_unused_1100_; lean_object* v_unused_1101_; lean_object* v_unused_1102_; 
v_unused_1098_ = lean_ctor_get(v_l_1048_, 4);
lean_dec(v_unused_1098_);
v_unused_1099_ = lean_ctor_get(v_l_1048_, 3);
lean_dec(v_unused_1099_);
v_unused_1100_ = lean_ctor_get(v_l_1048_, 2);
lean_dec(v_unused_1100_);
v_unused_1101_ = lean_ctor_get(v_l_1048_, 1);
lean_dec(v_unused_1101_);
v_unused_1102_ = lean_ctor_get(v_l_1048_, 0);
lean_dec(v_unused_1102_);
v___x_1071_ = v_l_1048_;
v_isShared_1072_ = v_isSharedCheck_1097_;
goto v_resetjp_1070_;
}
else
{
lean_dec(v_l_1048_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1097_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1087_; 
v___x_1073_ = lean_nat_add(v___x_1043_, v_size_1044_);
lean_dec(v_size_1044_);
v___x_1074_ = lean_nat_add(v___x_1073_, v_size_1045_);
lean_dec(v_size_1045_);
if (lean_obj_tag(v_l_1064_) == 0)
{
lean_object* v_size_1095_; 
v_size_1095_ = lean_ctor_get(v_l_1064_, 0);
lean_inc(v_size_1095_);
v___y_1087_ = v_size_1095_;
goto v___jp_1086_;
}
else
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_unsigned_to_nat(0u);
v___y_1087_ = v___x_1096_;
goto v___jp_1086_;
}
v___jp_1075_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = lean_nat_add(v___y_1076_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec(v___y_1076_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 4, v_r_1049_);
lean_ctor_set(v___x_1071_, 3, v_r_1065_);
lean_ctor_set(v___x_1071_, 2, v_v_1047_);
lean_ctor_set(v___x_1071_, 1, v_k_1046_);
lean_ctor_set(v___x_1071_, 0, v___x_1079_);
v___x_1081_ = v___x_1071_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_k_1046_);
lean_ctor_set(v_reuseFailAlloc_1085_, 2, v_v_1047_);
lean_ctor_set(v_reuseFailAlloc_1085_, 3, v_r_1065_);
lean_ctor_set(v_reuseFailAlloc_1085_, 4, v_r_1049_);
v___x_1081_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1083_; 
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 4, v___x_1081_);
lean_ctor_set(v___x_1059_, 3, v___y_1077_);
lean_ctor_set(v___x_1059_, 2, v_v_1063_);
lean_ctor_set(v___x_1059_, 1, v_k_1062_);
lean_ctor_set(v___x_1059_, 0, v___x_1074_);
v___x_1083_ = v___x_1059_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v_k_1062_);
lean_ctor_set(v_reuseFailAlloc_1084_, 2, v_v_1063_);
lean_ctor_set(v_reuseFailAlloc_1084_, 3, v___y_1077_);
lean_ctor_set(v_reuseFailAlloc_1084_, 4, v___x_1081_);
v___x_1083_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
return v___x_1083_;
}
}
}
v___jp_1086_:
{
lean_object* v___x_1088_; lean_object* v___x_1090_; 
v___x_1088_ = lean_nat_add(v___x_1073_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec(v___x_1073_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v_l_1064_);
lean_ctor_set(v___x_1039_, 3, v_impl_1042_);
lean_ctor_set(v___x_1039_, 0, v___x_1088_);
v___x_1090_ = v___x_1039_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1088_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1094_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1094_, 3, v_impl_1042_);
lean_ctor_set(v_reuseFailAlloc_1094_, 4, v_l_1064_);
v___x_1090_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_nat_add(v___x_1043_, v_size_1066_);
if (lean_obj_tag(v_r_1065_) == 0)
{
lean_object* v_size_1092_; 
v_size_1092_ = lean_ctor_get(v_r_1065_, 0);
lean_inc(v_size_1092_);
v___y_1076_ = v___x_1091_;
v___y_1077_ = v___x_1090_;
v___y_1078_ = v_size_1092_;
goto v___jp_1075_;
}
else
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_unsigned_to_nat(0u);
v___y_1076_ = v___x_1091_;
v___y_1077_ = v___x_1090_;
v___y_1078_ = v___x_1093_;
goto v___jp_1075_;
}
}
}
}
}
else
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1107_; 
lean_del_object(v___x_1039_);
v___x_1103_ = lean_nat_add(v___x_1043_, v_size_1044_);
lean_dec(v_size_1044_);
v___x_1104_ = lean_nat_add(v___x_1103_, v_size_1045_);
lean_dec(v_size_1045_);
v___x_1105_ = lean_nat_add(v___x_1103_, v_size_1061_);
lean_dec(v___x_1103_);
lean_inc_ref(v_impl_1042_);
if (v_isShared_1060_ == 0)
{
lean_ctor_set(v___x_1059_, 4, v_l_1048_);
lean_ctor_set(v___x_1059_, 3, v_impl_1042_);
lean_ctor_set(v___x_1059_, 2, v_v_1035_);
lean_ctor_set(v___x_1059_, 1, v_k_1034_);
lean_ctor_set(v___x_1059_, 0, v___x_1105_);
v___x_1107_ = v___x_1059_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1105_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1120_, 3, v_impl_1042_);
lean_ctor_set(v_reuseFailAlloc_1120_, 4, v_l_1048_);
v___x_1107_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v_isSharedCheck_1114_ = !lean_is_exclusive(v_impl_1042_);
if (v_isSharedCheck_1114_ == 0)
{
lean_object* v_unused_1115_; lean_object* v_unused_1116_; lean_object* v_unused_1117_; lean_object* v_unused_1118_; lean_object* v_unused_1119_; 
v_unused_1115_ = lean_ctor_get(v_impl_1042_, 4);
lean_dec(v_unused_1115_);
v_unused_1116_ = lean_ctor_get(v_impl_1042_, 3);
lean_dec(v_unused_1116_);
v_unused_1117_ = lean_ctor_get(v_impl_1042_, 2);
lean_dec(v_unused_1117_);
v_unused_1118_ = lean_ctor_get(v_impl_1042_, 1);
lean_dec(v_unused_1118_);
v_unused_1119_ = lean_ctor_get(v_impl_1042_, 0);
lean_dec(v_unused_1119_);
v___x_1109_ = v_impl_1042_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_dec(v_impl_1042_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 4, v_r_1049_);
lean_ctor_set(v___x_1109_, 3, v___x_1107_);
lean_ctor_set(v___x_1109_, 2, v_v_1047_);
lean_ctor_set(v___x_1109_, 1, v_k_1046_);
lean_ctor_set(v___x_1109_, 0, v___x_1104_);
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1104_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_k_1046_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_v_1047_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v_r_1049_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1127_; lean_object* v___x_1128_; lean_object* v___x_1130_; 
v_size_1127_ = lean_ctor_get(v_impl_1042_, 0);
lean_inc(v_size_1127_);
v___x_1128_ = lean_nat_add(v___x_1043_, v_size_1127_);
lean_dec(v_size_1127_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 3, v_impl_1042_);
lean_ctor_set(v___x_1039_, 0, v___x_1128_);
v___x_1130_ = v___x_1039_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v___x_1128_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1131_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1131_, 3, v_impl_1042_);
lean_ctor_set(v_reuseFailAlloc_1131_, 4, v_r_1037_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
}
else
{
if (lean_obj_tag(v_r_1037_) == 0)
{
lean_object* v_l_1132_; 
v_l_1132_ = lean_ctor_get(v_r_1037_, 3);
lean_inc(v_l_1132_);
if (lean_obj_tag(v_l_1132_) == 0)
{
lean_object* v_r_1133_; 
v_r_1133_ = lean_ctor_get(v_r_1037_, 4);
lean_inc(v_r_1133_);
if (lean_obj_tag(v_r_1133_) == 0)
{
lean_object* v_size_1134_; lean_object* v_k_1135_; lean_object* v_v_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1149_; 
v_size_1134_ = lean_ctor_get(v_r_1037_, 0);
v_k_1135_ = lean_ctor_get(v_r_1037_, 1);
v_v_1136_ = lean_ctor_get(v_r_1037_, 2);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_r_1037_);
if (v_isSharedCheck_1149_ == 0)
{
lean_object* v_unused_1150_; lean_object* v_unused_1151_; 
v_unused_1150_ = lean_ctor_get(v_r_1037_, 4);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_r_1037_, 3);
lean_dec(v_unused_1151_);
v___x_1138_ = v_r_1037_;
v_isShared_1139_ = v_isSharedCheck_1149_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_v_1136_);
lean_inc(v_k_1135_);
lean_inc(v_size_1134_);
lean_dec(v_r_1037_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1149_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v_size_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v_size_1140_ = lean_ctor_get(v_l_1132_, 0);
v___x_1141_ = lean_nat_add(v___x_1043_, v_size_1134_);
lean_dec(v_size_1134_);
v___x_1142_ = lean_nat_add(v___x_1043_, v_size_1140_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 4, v_l_1132_);
lean_ctor_set(v___x_1138_, 3, v_impl_1042_);
lean_ctor_set(v___x_1138_, 2, v_v_1035_);
lean_ctor_set(v___x_1138_, 1, v_k_1034_);
lean_ctor_set(v___x_1138_, 0, v___x_1142_);
v___x_1144_ = v___x_1138_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_impl_1042_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_l_1132_);
v___x_1144_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1146_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v_r_1133_);
lean_ctor_set(v___x_1039_, 3, v___x_1144_);
lean_ctor_set(v___x_1039_, 2, v_v_1136_);
lean_ctor_set(v___x_1039_, 1, v_k_1135_);
lean_ctor_set(v___x_1039_, 0, v___x_1141_);
v___x_1146_ = v___x_1039_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v___x_1141_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_k_1135_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_v_1136_);
lean_ctor_set(v_reuseFailAlloc_1147_, 3, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1147_, 4, v_r_1133_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
else
{
lean_object* v_k_1152_; lean_object* v_v_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1176_; 
v_k_1152_ = lean_ctor_get(v_r_1037_, 1);
v_v_1153_ = lean_ctor_get(v_r_1037_, 2);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_r_1037_);
if (v_isSharedCheck_1176_ == 0)
{
lean_object* v_unused_1177_; lean_object* v_unused_1178_; lean_object* v_unused_1179_; 
v_unused_1177_ = lean_ctor_get(v_r_1037_, 4);
lean_dec(v_unused_1177_);
v_unused_1178_ = lean_ctor_get(v_r_1037_, 3);
lean_dec(v_unused_1178_);
v_unused_1179_ = lean_ctor_get(v_r_1037_, 0);
lean_dec(v_unused_1179_);
v___x_1155_ = v_r_1037_;
v_isShared_1156_ = v_isSharedCheck_1176_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_v_1153_);
lean_inc(v_k_1152_);
lean_dec(v_r_1037_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1176_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v_k_1157_; lean_object* v_v_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1172_; 
v_k_1157_ = lean_ctor_get(v_l_1132_, 1);
v_v_1158_ = lean_ctor_get(v_l_1132_, 2);
v_isSharedCheck_1172_ = !lean_is_exclusive(v_l_1132_);
if (v_isSharedCheck_1172_ == 0)
{
lean_object* v_unused_1173_; lean_object* v_unused_1174_; lean_object* v_unused_1175_; 
v_unused_1173_ = lean_ctor_get(v_l_1132_, 4);
lean_dec(v_unused_1173_);
v_unused_1174_ = lean_ctor_get(v_l_1132_, 3);
lean_dec(v_unused_1174_);
v_unused_1175_ = lean_ctor_get(v_l_1132_, 0);
lean_dec(v_unused_1175_);
v___x_1160_ = v_l_1132_;
v_isShared_1161_ = v_isSharedCheck_1172_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_v_1158_);
lean_inc(v_k_1157_);
lean_dec(v_l_1132_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1172_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = lean_unsigned_to_nat(3u);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 4, v_r_1133_);
lean_ctor_set(v___x_1160_, 3, v_r_1133_);
lean_ctor_set(v___x_1160_, 2, v_v_1035_);
lean_ctor_set(v___x_1160_, 1, v_k_1034_);
lean_ctor_set(v___x_1160_, 0, v___x_1043_);
v___x_1164_ = v___x_1160_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1171_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1171_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1171_, 3, v_r_1133_);
lean_ctor_set(v_reuseFailAlloc_1171_, 4, v_r_1133_);
v___x_1164_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1166_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 3, v_r_1133_);
lean_ctor_set(v___x_1155_, 0, v___x_1043_);
v___x_1166_ = v___x_1155_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_k_1152_);
lean_ctor_set(v_reuseFailAlloc_1170_, 2, v_v_1153_);
lean_ctor_set(v_reuseFailAlloc_1170_, 3, v_r_1133_);
lean_ctor_set(v_reuseFailAlloc_1170_, 4, v_r_1133_);
v___x_1166_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
lean_object* v___x_1168_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v___x_1166_);
lean_ctor_set(v___x_1039_, 3, v___x_1164_);
lean_ctor_set(v___x_1039_, 2, v_v_1158_);
lean_ctor_set(v___x_1039_, 1, v_k_1157_);
lean_ctor_set(v___x_1039_, 0, v___x_1162_);
v___x_1168_ = v___x_1039_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_k_1157_);
lean_ctor_set(v_reuseFailAlloc_1169_, 2, v_v_1158_);
lean_ctor_set(v_reuseFailAlloc_1169_, 3, v___x_1164_);
lean_ctor_set(v_reuseFailAlloc_1169_, 4, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
}
}
else
{
lean_object* v_r_1180_; 
v_r_1180_ = lean_ctor_get(v_r_1037_, 4);
lean_inc(v_r_1180_);
if (lean_obj_tag(v_r_1180_) == 0)
{
lean_object* v_k_1181_; lean_object* v_v_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1193_; 
v_k_1181_ = lean_ctor_get(v_r_1037_, 1);
v_v_1182_ = lean_ctor_get(v_r_1037_, 2);
v_isSharedCheck_1193_ = !lean_is_exclusive(v_r_1037_);
if (v_isSharedCheck_1193_ == 0)
{
lean_object* v_unused_1194_; lean_object* v_unused_1195_; lean_object* v_unused_1196_; 
v_unused_1194_ = lean_ctor_get(v_r_1037_, 4);
lean_dec(v_unused_1194_);
v_unused_1195_ = lean_ctor_get(v_r_1037_, 3);
lean_dec(v_unused_1195_);
v_unused_1196_ = lean_ctor_get(v_r_1037_, 0);
lean_dec(v_unused_1196_);
v___x_1184_ = v_r_1037_;
v_isShared_1185_ = v_isSharedCheck_1193_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_v_1182_);
lean_inc(v_k_1181_);
lean_dec(v_r_1037_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1193_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; lean_object* v___x_1188_; 
v___x_1186_ = lean_unsigned_to_nat(3u);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 4, v_l_1132_);
lean_ctor_set(v___x_1184_, 2, v_v_1035_);
lean_ctor_set(v___x_1184_, 1, v_k_1034_);
lean_ctor_set(v___x_1184_, 0, v___x_1043_);
v___x_1188_ = v___x_1184_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1192_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1192_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1192_, 3, v_l_1132_);
lean_ctor_set(v_reuseFailAlloc_1192_, 4, v_l_1132_);
v___x_1188_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
lean_object* v___x_1190_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v_r_1180_);
lean_ctor_set(v___x_1039_, 3, v___x_1188_);
lean_ctor_set(v___x_1039_, 2, v_v_1182_);
lean_ctor_set(v___x_1039_, 1, v_k_1181_);
lean_ctor_set(v___x_1039_, 0, v___x_1186_);
v___x_1190_ = v___x_1039_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1191_; 
v_reuseFailAlloc_1191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1191_, 0, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1191_, 1, v_k_1181_);
lean_ctor_set(v_reuseFailAlloc_1191_, 2, v_v_1182_);
lean_ctor_set(v_reuseFailAlloc_1191_, 3, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1191_, 4, v_r_1180_);
v___x_1190_ = v_reuseFailAlloc_1191_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
return v___x_1190_;
}
}
}
}
else
{
lean_object* v_size_1197_; lean_object* v_k_1198_; lean_object* v_v_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1210_; 
v_size_1197_ = lean_ctor_get(v_r_1037_, 0);
v_k_1198_ = lean_ctor_get(v_r_1037_, 1);
v_v_1199_ = lean_ctor_get(v_r_1037_, 2);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_r_1037_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; lean_object* v_unused_1212_; 
v_unused_1211_ = lean_ctor_get(v_r_1037_, 4);
lean_dec(v_unused_1211_);
v_unused_1212_ = lean_ctor_get(v_r_1037_, 3);
lean_dec(v_unused_1212_);
v___x_1201_ = v_r_1037_;
v_isShared_1202_ = v_isSharedCheck_1210_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_v_1199_);
lean_inc(v_k_1198_);
lean_inc(v_size_1197_);
lean_dec(v_r_1037_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1210_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 3, v_r_1180_);
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_size_1197_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_k_1198_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_v_1199_);
lean_ctor_set(v_reuseFailAlloc_1209_, 3, v_r_1180_);
lean_ctor_set(v_reuseFailAlloc_1209_, 4, v_r_1180_);
v___x_1204_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1205_ = lean_unsigned_to_nat(2u);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v___x_1204_);
lean_ctor_set(v___x_1039_, 3, v_r_1180_);
lean_ctor_set(v___x_1039_, 0, v___x_1205_);
v___x_1207_ = v___x_1039_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_r_1180_);
lean_ctor_set(v_reuseFailAlloc_1208_, 4, v___x_1204_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
}
else
{
lean_object* v___x_1214_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 3, v_r_1037_);
lean_ctor_set(v___x_1039_, 0, v___x_1043_);
v___x_1214_ = v___x_1039_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v___x_1043_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1215_, 3, v_r_1037_);
lean_ctor_set(v_reuseFailAlloc_1215_, 4, v_r_1037_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
case 1:
{
lean_del_object(v___x_1039_);
lean_dec(v_v_1035_);
lean_dec(v_k_1034_);
if (lean_obj_tag(v_l_1036_) == 0)
{
if (lean_obj_tag(v_r_1037_) == 0)
{
lean_object* v_size_1216_; lean_object* v_k_1217_; lean_object* v_v_1218_; lean_object* v_l_1219_; lean_object* v_r_1220_; lean_object* v_size_1221_; lean_object* v_k_1222_; lean_object* v_v_1223_; lean_object* v_l_1224_; lean_object* v_r_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; 
v_size_1216_ = lean_ctor_get(v_l_1036_, 0);
v_k_1217_ = lean_ctor_get(v_l_1036_, 1);
v_v_1218_ = lean_ctor_get(v_l_1036_, 2);
v_l_1219_ = lean_ctor_get(v_l_1036_, 3);
v_r_1220_ = lean_ctor_get(v_l_1036_, 4);
lean_inc(v_r_1220_);
v_size_1221_ = lean_ctor_get(v_r_1037_, 0);
v_k_1222_ = lean_ctor_get(v_r_1037_, 1);
v_v_1223_ = lean_ctor_get(v_r_1037_, 2);
v_l_1224_ = lean_ctor_get(v_r_1037_, 3);
lean_inc(v_l_1224_);
v_r_1225_ = lean_ctor_get(v_r_1037_, 4);
v___x_1226_ = lean_unsigned_to_nat(1u);
v___x_1227_ = lean_nat_dec_lt(v_size_1216_, v_size_1221_);
if (v___x_1227_ == 0)
{
lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1363_; 
lean_inc(v_l_1219_);
lean_inc(v_v_1218_);
lean_inc(v_k_1217_);
v_isSharedCheck_1363_ = !lean_is_exclusive(v_l_1036_);
if (v_isSharedCheck_1363_ == 0)
{
lean_object* v_unused_1364_; lean_object* v_unused_1365_; lean_object* v_unused_1366_; lean_object* v_unused_1367_; lean_object* v_unused_1368_; 
v_unused_1364_ = lean_ctor_get(v_l_1036_, 4);
lean_dec(v_unused_1364_);
v_unused_1365_ = lean_ctor_get(v_l_1036_, 3);
lean_dec(v_unused_1365_);
v_unused_1366_ = lean_ctor_get(v_l_1036_, 2);
lean_dec(v_unused_1366_);
v_unused_1367_ = lean_ctor_get(v_l_1036_, 1);
lean_dec(v_unused_1367_);
v_unused_1368_ = lean_ctor_get(v_l_1036_, 0);
lean_dec(v_unused_1368_);
v___x_1229_ = v_l_1036_;
v_isShared_1230_ = v_isSharedCheck_1363_;
goto v_resetjp_1228_;
}
else
{
lean_dec(v_l_1036_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1363_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v_tree_1232_; 
v___x_1231_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(v_k_1217_, v_v_1218_, v_l_1219_, v_r_1220_);
v_tree_1232_ = lean_ctor_get(v___x_1231_, 2);
lean_inc(v_tree_1232_);
if (lean_obj_tag(v_tree_1232_) == 0)
{
lean_object* v_k_1233_; lean_object* v_v_1234_; lean_object* v_size_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; 
v_k_1233_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_k_1233_);
v_v_1234_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_v_1234_);
lean_dec_ref(v___x_1231_);
v_size_1235_ = lean_ctor_get(v_tree_1232_, 0);
v___x_1236_ = lean_unsigned_to_nat(3u);
v___x_1237_ = lean_nat_mul(v___x_1236_, v_size_1235_);
v___x_1238_ = lean_nat_dec_lt(v___x_1237_, v_size_1221_);
lean_dec(v___x_1237_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
lean_dec(v_l_1224_);
v___x_1239_ = lean_nat_add(v___x_1226_, v_size_1235_);
v___x_1240_ = lean_nat_add(v___x_1239_, v_size_1221_);
lean_dec(v___x_1239_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 4, v_r_1037_);
lean_ctor_set(v___x_1229_, 3, v_tree_1232_);
lean_ctor_set(v___x_1229_, 2, v_v_1234_);
lean_ctor_set(v___x_1229_, 1, v_k_1233_);
lean_ctor_set(v___x_1229_, 0, v___x_1240_);
v___x_1242_ = v___x_1229_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v_k_1233_);
lean_ctor_set(v_reuseFailAlloc_1243_, 2, v_v_1234_);
lean_ctor_set(v_reuseFailAlloc_1243_, 3, v_tree_1232_);
lean_ctor_set(v_reuseFailAlloc_1243_, 4, v_r_1037_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
else
{
lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1298_; 
lean_inc(v_r_1225_);
lean_inc(v_v_1223_);
lean_inc(v_k_1222_);
lean_inc(v_size_1221_);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_r_1037_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; lean_object* v_unused_1300_; lean_object* v_unused_1301_; lean_object* v_unused_1302_; lean_object* v_unused_1303_; 
v_unused_1299_ = lean_ctor_get(v_r_1037_, 4);
lean_dec(v_unused_1299_);
v_unused_1300_ = lean_ctor_get(v_r_1037_, 3);
lean_dec(v_unused_1300_);
v_unused_1301_ = lean_ctor_get(v_r_1037_, 2);
lean_dec(v_unused_1301_);
v_unused_1302_ = lean_ctor_get(v_r_1037_, 1);
lean_dec(v_unused_1302_);
v_unused_1303_ = lean_ctor_get(v_r_1037_, 0);
lean_dec(v_unused_1303_);
v___x_1245_ = v_r_1037_;
v_isShared_1246_ = v_isSharedCheck_1298_;
goto v_resetjp_1244_;
}
else
{
lean_dec(v_r_1037_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1298_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v_size_1247_; lean_object* v_k_1248_; lean_object* v_v_1249_; lean_object* v_l_1250_; lean_object* v_r_1251_; lean_object* v_size_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; uint8_t v___x_1255_; 
v_size_1247_ = lean_ctor_get(v_l_1224_, 0);
v_k_1248_ = lean_ctor_get(v_l_1224_, 1);
v_v_1249_ = lean_ctor_get(v_l_1224_, 2);
v_l_1250_ = lean_ctor_get(v_l_1224_, 3);
v_r_1251_ = lean_ctor_get(v_l_1224_, 4);
v_size_1252_ = lean_ctor_get(v_r_1225_, 0);
v___x_1253_ = lean_unsigned_to_nat(2u);
v___x_1254_ = lean_nat_mul(v___x_1253_, v_size_1252_);
v___x_1255_ = lean_nat_dec_lt(v_size_1247_, v___x_1254_);
lean_dec(v___x_1254_);
if (v___x_1255_ == 0)
{
lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1283_; 
lean_inc(v_r_1251_);
lean_inc(v_l_1250_);
lean_inc(v_v_1249_);
lean_inc(v_k_1248_);
v_isSharedCheck_1283_ = !lean_is_exclusive(v_l_1224_);
if (v_isSharedCheck_1283_ == 0)
{
lean_object* v_unused_1284_; lean_object* v_unused_1285_; lean_object* v_unused_1286_; lean_object* v_unused_1287_; lean_object* v_unused_1288_; 
v_unused_1284_ = lean_ctor_get(v_l_1224_, 4);
lean_dec(v_unused_1284_);
v_unused_1285_ = lean_ctor_get(v_l_1224_, 3);
lean_dec(v_unused_1285_);
v_unused_1286_ = lean_ctor_get(v_l_1224_, 2);
lean_dec(v_unused_1286_);
v_unused_1287_ = lean_ctor_get(v_l_1224_, 1);
lean_dec(v_unused_1287_);
v_unused_1288_ = lean_ctor_get(v_l_1224_, 0);
lean_dec(v_unused_1288_);
v___x_1257_ = v_l_1224_;
v_isShared_1258_ = v_isSharedCheck_1283_;
goto v_resetjp_1256_;
}
else
{
lean_dec(v_l_1224_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1283_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1273_; 
v___x_1259_ = lean_nat_add(v___x_1226_, v_size_1235_);
v___x_1260_ = lean_nat_add(v___x_1259_, v_size_1221_);
lean_dec(v_size_1221_);
if (lean_obj_tag(v_l_1250_) == 0)
{
lean_object* v_size_1281_; 
v_size_1281_ = lean_ctor_get(v_l_1250_, 0);
lean_inc(v_size_1281_);
v___y_1273_ = v_size_1281_;
goto v___jp_1272_;
}
else
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_unsigned_to_nat(0u);
v___y_1273_ = v___x_1282_;
goto v___jp_1272_;
}
v___jp_1261_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = lean_nat_add(v___y_1262_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec(v___y_1262_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 4, v_r_1225_);
lean_ctor_set(v___x_1257_, 3, v_r_1251_);
lean_ctor_set(v___x_1257_, 2, v_v_1223_);
lean_ctor_set(v___x_1257_, 1, v_k_1222_);
lean_ctor_set(v___x_1257_, 0, v___x_1265_);
v___x_1267_ = v___x_1257_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_k_1222_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_v_1223_);
lean_ctor_set(v_reuseFailAlloc_1271_, 3, v_r_1251_);
lean_ctor_set(v_reuseFailAlloc_1271_, 4, v_r_1225_);
v___x_1267_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1269_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 4, v___x_1267_);
lean_ctor_set(v___x_1245_, 3, v___y_1263_);
lean_ctor_set(v___x_1245_, 2, v_v_1249_);
lean_ctor_set(v___x_1245_, 1, v_k_1248_);
lean_ctor_set(v___x_1245_, 0, v___x_1260_);
v___x_1269_ = v___x_1245_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_k_1248_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_v_1249_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v___y_1263_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
v___jp_1272_:
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1274_ = lean_nat_add(v___x_1259_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec(v___x_1259_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 4, v_l_1250_);
lean_ctor_set(v___x_1229_, 3, v_tree_1232_);
lean_ctor_set(v___x_1229_, 2, v_v_1234_);
lean_ctor_set(v___x_1229_, 1, v_k_1233_);
lean_ctor_set(v___x_1229_, 0, v___x_1274_);
v___x_1276_ = v___x_1229_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_k_1233_);
lean_ctor_set(v_reuseFailAlloc_1280_, 2, v_v_1234_);
lean_ctor_set(v_reuseFailAlloc_1280_, 3, v_tree_1232_);
lean_ctor_set(v_reuseFailAlloc_1280_, 4, v_l_1250_);
v___x_1276_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1277_; 
v___x_1277_ = lean_nat_add(v___x_1226_, v_size_1252_);
if (lean_obj_tag(v_r_1251_) == 0)
{
lean_object* v_size_1278_; 
v_size_1278_ = lean_ctor_get(v_r_1251_, 0);
lean_inc(v_size_1278_);
v___y_1262_ = v___x_1277_;
v___y_1263_ = v___x_1276_;
v___y_1264_ = v_size_1278_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_unsigned_to_nat(0u);
v___y_1262_ = v___x_1277_;
v___y_1263_ = v___x_1276_;
v___y_1264_ = v___x_1279_;
goto v___jp_1261_;
}
}
}
}
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1293_; 
v___x_1289_ = lean_nat_add(v___x_1226_, v_size_1235_);
v___x_1290_ = lean_nat_add(v___x_1289_, v_size_1221_);
lean_dec(v_size_1221_);
v___x_1291_ = lean_nat_add(v___x_1289_, v_size_1247_);
lean_dec(v___x_1289_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 4, v_l_1224_);
lean_ctor_set(v___x_1245_, 3, v_tree_1232_);
lean_ctor_set(v___x_1245_, 2, v_v_1234_);
lean_ctor_set(v___x_1245_, 1, v_k_1233_);
lean_ctor_set(v___x_1245_, 0, v___x_1291_);
v___x_1293_ = v___x_1245_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1291_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_k_1233_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v_v_1234_);
lean_ctor_set(v_reuseFailAlloc_1297_, 3, v_tree_1232_);
lean_ctor_set(v_reuseFailAlloc_1297_, 4, v_l_1224_);
v___x_1293_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
lean_object* v___x_1295_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 4, v_r_1225_);
lean_ctor_set(v___x_1229_, 3, v___x_1293_);
lean_ctor_set(v___x_1229_, 2, v_v_1223_);
lean_ctor_set(v___x_1229_, 1, v_k_1222_);
lean_ctor_set(v___x_1229_, 0, v___x_1290_);
v___x_1295_ = v___x_1229_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_k_1222_);
lean_ctor_set(v_reuseFailAlloc_1296_, 2, v_v_1223_);
lean_ctor_set(v_reuseFailAlloc_1296_, 3, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1296_, 4, v_r_1225_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
}
else
{
lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1357_; 
lean_inc(v_r_1225_);
lean_inc(v_v_1223_);
lean_inc(v_k_1222_);
lean_inc(v_size_1221_);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_r_1037_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; lean_object* v_unused_1359_; lean_object* v_unused_1360_; lean_object* v_unused_1361_; lean_object* v_unused_1362_; 
v_unused_1358_ = lean_ctor_get(v_r_1037_, 4);
lean_dec(v_unused_1358_);
v_unused_1359_ = lean_ctor_get(v_r_1037_, 3);
lean_dec(v_unused_1359_);
v_unused_1360_ = lean_ctor_get(v_r_1037_, 2);
lean_dec(v_unused_1360_);
v_unused_1361_ = lean_ctor_get(v_r_1037_, 1);
lean_dec(v_unused_1361_);
v_unused_1362_ = lean_ctor_get(v_r_1037_, 0);
lean_dec(v_unused_1362_);
v___x_1305_ = v_r_1037_;
v_isShared_1306_ = v_isSharedCheck_1357_;
goto v_resetjp_1304_;
}
else
{
lean_dec(v_r_1037_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1357_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
if (lean_obj_tag(v_l_1224_) == 0)
{
if (lean_obj_tag(v_r_1225_) == 0)
{
lean_object* v_k_1307_; lean_object* v_v_1308_; lean_object* v_size_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; 
v_k_1307_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_k_1307_);
v_v_1308_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_v_1308_);
lean_dec_ref(v___x_1231_);
v_size_1309_ = lean_ctor_get(v_l_1224_, 0);
v___x_1310_ = lean_nat_add(v___x_1226_, v_size_1221_);
lean_dec(v_size_1221_);
v___x_1311_ = lean_nat_add(v___x_1226_, v_size_1309_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 4, v_l_1224_);
lean_ctor_set(v___x_1305_, 3, v_tree_1232_);
lean_ctor_set(v___x_1305_, 2, v_v_1308_);
lean_ctor_set(v___x_1305_, 1, v_k_1307_);
lean_ctor_set(v___x_1305_, 0, v___x_1311_);
v___x_1313_ = v___x_1305_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1311_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_k_1307_);
lean_ctor_set(v_reuseFailAlloc_1317_, 2, v_v_1308_);
lean_ctor_set(v_reuseFailAlloc_1317_, 3, v_tree_1232_);
lean_ctor_set(v_reuseFailAlloc_1317_, 4, v_l_1224_);
v___x_1313_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
lean_object* v___x_1315_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 4, v_r_1225_);
lean_ctor_set(v___x_1229_, 3, v___x_1313_);
lean_ctor_set(v___x_1229_, 2, v_v_1223_);
lean_ctor_set(v___x_1229_, 1, v_k_1222_);
lean_ctor_set(v___x_1229_, 0, v___x_1310_);
v___x_1315_ = v___x_1229_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1310_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_k_1222_);
lean_ctor_set(v_reuseFailAlloc_1316_, 2, v_v_1223_);
lean_ctor_set(v_reuseFailAlloc_1316_, 3, v___x_1313_);
lean_ctor_set(v_reuseFailAlloc_1316_, 4, v_r_1225_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
else
{
lean_object* v_k_1318_; lean_object* v_v_1319_; lean_object* v_k_1320_; lean_object* v_v_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1335_; 
lean_dec(v_size_1221_);
v_k_1318_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_k_1318_);
v_v_1319_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_v_1319_);
lean_dec_ref(v___x_1231_);
v_k_1320_ = lean_ctor_get(v_l_1224_, 1);
v_v_1321_ = lean_ctor_get(v_l_1224_, 2);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_l_1224_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; lean_object* v_unused_1337_; lean_object* v_unused_1338_; 
v_unused_1336_ = lean_ctor_get(v_l_1224_, 4);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v_l_1224_, 3);
lean_dec(v_unused_1337_);
v_unused_1338_ = lean_ctor_get(v_l_1224_, 0);
lean_dec(v_unused_1338_);
v___x_1323_ = v_l_1224_;
v_isShared_1324_ = v_isSharedCheck_1335_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_v_1321_);
lean_inc(v_k_1320_);
lean_dec(v_l_1224_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1335_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1325_ = lean_unsigned_to_nat(3u);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 4, v_r_1225_);
lean_ctor_set(v___x_1323_, 3, v_r_1225_);
lean_ctor_set(v___x_1323_, 2, v_v_1319_);
lean_ctor_set(v___x_1323_, 1, v_k_1318_);
lean_ctor_set(v___x_1323_, 0, v___x_1226_);
v___x_1327_ = v___x_1323_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1334_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1334_, 3, v_r_1225_);
lean_ctor_set(v_reuseFailAlloc_1334_, 4, v_r_1225_);
v___x_1327_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1329_; 
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 3, v_r_1225_);
lean_ctor_set(v___x_1305_, 0, v___x_1226_);
v___x_1329_ = v___x_1305_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_k_1222_);
lean_ctor_set(v_reuseFailAlloc_1333_, 2, v_v_1223_);
lean_ctor_set(v_reuseFailAlloc_1333_, 3, v_r_1225_);
lean_ctor_set(v_reuseFailAlloc_1333_, 4, v_r_1225_);
v___x_1329_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1331_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 4, v___x_1329_);
lean_ctor_set(v___x_1229_, 3, v___x_1327_);
lean_ctor_set(v___x_1229_, 2, v_v_1321_);
lean_ctor_set(v___x_1229_, 1, v_k_1320_);
lean_ctor_set(v___x_1229_, 0, v___x_1325_);
v___x_1331_ = v___x_1229_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_k_1320_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_v_1321_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1225_) == 0)
{
lean_object* v_k_1339_; lean_object* v_v_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; 
lean_dec(v_size_1221_);
v_k_1339_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_k_1339_);
v_v_1340_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_v_1340_);
lean_dec_ref(v___x_1231_);
v___x_1341_ = lean_unsigned_to_nat(3u);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 4, v_l_1224_);
lean_ctor_set(v___x_1305_, 2, v_v_1340_);
lean_ctor_set(v___x_1305_, 1, v_k_1339_);
lean_ctor_set(v___x_1305_, 0, v___x_1226_);
v___x_1343_ = v___x_1305_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_k_1339_);
lean_ctor_set(v_reuseFailAlloc_1347_, 2, v_v_1340_);
lean_ctor_set(v_reuseFailAlloc_1347_, 3, v_l_1224_);
lean_ctor_set(v_reuseFailAlloc_1347_, 4, v_l_1224_);
v___x_1343_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1345_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 4, v_r_1225_);
lean_ctor_set(v___x_1229_, 3, v___x_1343_);
lean_ctor_set(v___x_1229_, 2, v_v_1223_);
lean_ctor_set(v___x_1229_, 1, v_k_1222_);
lean_ctor_set(v___x_1229_, 0, v___x_1341_);
v___x_1345_ = v___x_1229_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1341_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_k_1222_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_v_1223_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v___x_1343_);
lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_r_1225_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
else
{
lean_object* v_k_1348_; lean_object* v_v_1349_; lean_object* v___x_1351_; 
v_k_1348_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_k_1348_);
v_v_1349_ = lean_ctor_get(v___x_1231_, 1);
lean_inc(v_v_1349_);
lean_dec_ref(v___x_1231_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 3, v_r_1225_);
v___x_1351_ = v___x_1305_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_size_1221_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_k_1222_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_v_1223_);
lean_ctor_set(v_reuseFailAlloc_1356_, 3, v_r_1225_);
lean_ctor_set(v_reuseFailAlloc_1356_, 4, v_r_1225_);
v___x_1351_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1352_ = lean_unsigned_to_nat(2u);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 4, v___x_1351_);
lean_ctor_set(v___x_1229_, 3, v_r_1225_);
lean_ctor_set(v___x_1229_, 2, v_v_1349_);
lean_ctor_set(v___x_1229_, 1, v_k_1348_);
lean_ctor_set(v___x_1229_, 0, v___x_1352_);
v___x_1354_ = v___x_1229_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_k_1348_);
lean_ctor_set(v_reuseFailAlloc_1355_, 2, v_v_1349_);
lean_ctor_set(v_reuseFailAlloc_1355_, 3, v_r_1225_);
lean_ctor_set(v_reuseFailAlloc_1355_, 4, v___x_1351_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
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
lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1521_; 
lean_inc(v_r_1225_);
lean_inc(v_v_1223_);
lean_inc(v_k_1222_);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_r_1037_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; lean_object* v_unused_1523_; lean_object* v_unused_1524_; lean_object* v_unused_1525_; lean_object* v_unused_1526_; 
v_unused_1522_ = lean_ctor_get(v_r_1037_, 4);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_r_1037_, 3);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v_r_1037_, 2);
lean_dec(v_unused_1524_);
v_unused_1525_ = lean_ctor_get(v_r_1037_, 1);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v_r_1037_, 0);
lean_dec(v_unused_1526_);
v___x_1370_ = v_r_1037_;
v_isShared_1371_ = v_isSharedCheck_1521_;
goto v_resetjp_1369_;
}
else
{
lean_dec(v_r_1037_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1521_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v_tree_1373_; 
v___x_1372_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(v_k_1222_, v_v_1223_, v_l_1224_, v_r_1225_);
v_tree_1373_ = lean_ctor_get(v___x_1372_, 2);
lean_inc(v_tree_1373_);
if (lean_obj_tag(v_tree_1373_) == 0)
{
lean_object* v_k_1374_; lean_object* v_v_1375_; lean_object* v_size_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; uint8_t v___x_1379_; 
v_k_1374_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_k_1374_);
v_v_1375_ = lean_ctor_get(v___x_1372_, 1);
lean_inc(v_v_1375_);
lean_dec_ref(v___x_1372_);
v_size_1376_ = lean_ctor_get(v_tree_1373_, 0);
v___x_1377_ = lean_unsigned_to_nat(3u);
v___x_1378_ = lean_nat_mul(v___x_1377_, v_size_1376_);
v___x_1379_ = lean_nat_dec_lt(v___x_1378_, v_size_1216_);
lean_dec(v___x_1378_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1383_; 
lean_dec(v_r_1220_);
v___x_1380_ = lean_nat_add(v___x_1226_, v_size_1216_);
v___x_1381_ = lean_nat_add(v___x_1380_, v_size_1376_);
lean_dec(v___x_1380_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v_tree_1373_);
lean_ctor_set(v___x_1370_, 3, v_l_1036_);
lean_ctor_set(v___x_1370_, 2, v_v_1375_);
lean_ctor_set(v___x_1370_, 1, v_k_1374_);
lean_ctor_set(v___x_1370_, 0, v___x_1381_);
v___x_1383_ = v___x_1370_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1384_, 3, v_l_1036_);
lean_ctor_set(v_reuseFailAlloc_1384_, 4, v_tree_1373_);
v___x_1383_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
return v___x_1383_;
}
}
else
{
lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1450_; 
lean_inc(v_l_1219_);
lean_inc(v_v_1218_);
lean_inc(v_k_1217_);
lean_inc(v_size_1216_);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_l_1036_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; lean_object* v_unused_1452_; lean_object* v_unused_1453_; lean_object* v_unused_1454_; lean_object* v_unused_1455_; 
v_unused_1451_ = lean_ctor_get(v_l_1036_, 4);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_l_1036_, 3);
lean_dec(v_unused_1452_);
v_unused_1453_ = lean_ctor_get(v_l_1036_, 2);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_l_1036_, 1);
lean_dec(v_unused_1454_);
v_unused_1455_ = lean_ctor_get(v_l_1036_, 0);
lean_dec(v_unused_1455_);
v___x_1386_ = v_l_1036_;
v_isShared_1387_ = v_isSharedCheck_1450_;
goto v_resetjp_1385_;
}
else
{
lean_dec(v_l_1036_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1450_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v_size_1388_; lean_object* v_size_1389_; lean_object* v_k_1390_; lean_object* v_v_1391_; lean_object* v_l_1392_; lean_object* v_r_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; 
v_size_1388_ = lean_ctor_get(v_l_1219_, 0);
v_size_1389_ = lean_ctor_get(v_r_1220_, 0);
v_k_1390_ = lean_ctor_get(v_r_1220_, 1);
v_v_1391_ = lean_ctor_get(v_r_1220_, 2);
v_l_1392_ = lean_ctor_get(v_r_1220_, 3);
v_r_1393_ = lean_ctor_get(v_r_1220_, 4);
v___x_1394_ = lean_unsigned_to_nat(2u);
v___x_1395_ = lean_nat_mul(v___x_1394_, v_size_1388_);
v___x_1396_ = lean_nat_dec_lt(v_size_1389_, v___x_1395_);
lean_dec(v___x_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1434_; 
lean_inc(v_r_1393_);
lean_inc(v_l_1392_);
lean_inc(v_v_1391_);
lean_inc(v_k_1390_);
lean_del_object(v___x_1386_);
v_isSharedCheck_1434_ = !lean_is_exclusive(v_r_1220_);
if (v_isSharedCheck_1434_ == 0)
{
lean_object* v_unused_1435_; lean_object* v_unused_1436_; lean_object* v_unused_1437_; lean_object* v_unused_1438_; lean_object* v_unused_1439_; 
v_unused_1435_ = lean_ctor_get(v_r_1220_, 4);
lean_dec(v_unused_1435_);
v_unused_1436_ = lean_ctor_get(v_r_1220_, 3);
lean_dec(v_unused_1436_);
v_unused_1437_ = lean_ctor_get(v_r_1220_, 2);
lean_dec(v_unused_1437_);
v_unused_1438_ = lean_ctor_get(v_r_1220_, 1);
lean_dec(v_unused_1438_);
v_unused_1439_ = lean_ctor_get(v_r_1220_, 0);
lean_dec(v_unused_1439_);
v___x_1398_ = v_r_1220_;
v_isShared_1399_ = v_isSharedCheck_1434_;
goto v_resetjp_1397_;
}
else
{
lean_dec(v_r_1220_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1434_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; lean_object* v___x_1422_; lean_object* v___y_1424_; 
v___x_1400_ = lean_nat_add(v___x_1226_, v_size_1216_);
lean_dec(v_size_1216_);
v___x_1401_ = lean_nat_add(v___x_1400_, v_size_1376_);
lean_dec(v___x_1400_);
v___x_1422_ = lean_nat_add(v___x_1226_, v_size_1388_);
if (lean_obj_tag(v_l_1392_) == 0)
{
lean_object* v_size_1432_; 
v_size_1432_ = lean_ctor_get(v_l_1392_, 0);
lean_inc(v_size_1432_);
v___y_1424_ = v_size_1432_;
goto v___jp_1423_;
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_unsigned_to_nat(0u);
v___y_1424_ = v___x_1433_;
goto v___jp_1423_;
}
v___jp_1402_:
{
lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1406_ = lean_nat_add(v___y_1403_, v___y_1405_);
lean_dec(v___y_1405_);
lean_dec(v___y_1403_);
lean_inc_ref(v_tree_1373_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 4, v_tree_1373_);
lean_ctor_set(v___x_1398_, 3, v_r_1393_);
lean_ctor_set(v___x_1398_, 2, v_v_1375_);
lean_ctor_set(v___x_1398_, 1, v_k_1374_);
lean_ctor_set(v___x_1398_, 0, v___x_1406_);
v___x_1408_ = v___x_1398_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1421_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1421_, 3, v_r_1393_);
lean_ctor_set(v_reuseFailAlloc_1421_, 4, v_tree_1373_);
v___x_1408_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
v_isSharedCheck_1415_ = !lean_is_exclusive(v_tree_1373_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; lean_object* v_unused_1417_; lean_object* v_unused_1418_; lean_object* v_unused_1419_; lean_object* v_unused_1420_; 
v_unused_1416_ = lean_ctor_get(v_tree_1373_, 4);
lean_dec(v_unused_1416_);
v_unused_1417_ = lean_ctor_get(v_tree_1373_, 3);
lean_dec(v_unused_1417_);
v_unused_1418_ = lean_ctor_get(v_tree_1373_, 2);
lean_dec(v_unused_1418_);
v_unused_1419_ = lean_ctor_get(v_tree_1373_, 1);
lean_dec(v_unused_1419_);
v_unused_1420_ = lean_ctor_get(v_tree_1373_, 0);
lean_dec(v_unused_1420_);
v___x_1410_ = v_tree_1373_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_dec(v_tree_1373_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 4, v___x_1408_);
lean_ctor_set(v___x_1410_, 3, v___y_1404_);
lean_ctor_set(v___x_1410_, 2, v_v_1391_);
lean_ctor_set(v___x_1410_, 1, v_k_1390_);
lean_ctor_set(v___x_1410_, 0, v___x_1401_);
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v_k_1390_);
lean_ctor_set(v_reuseFailAlloc_1414_, 2, v_v_1391_);
lean_ctor_set(v_reuseFailAlloc_1414_, 3, v___y_1404_);
lean_ctor_set(v_reuseFailAlloc_1414_, 4, v___x_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
v___jp_1423_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = lean_nat_add(v___x_1422_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec(v___x_1422_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v_l_1392_);
lean_ctor_set(v___x_1370_, 3, v_l_1219_);
lean_ctor_set(v___x_1370_, 2, v_v_1218_);
lean_ctor_set(v___x_1370_, 1, v_k_1217_);
lean_ctor_set(v___x_1370_, 0, v___x_1425_);
v___x_1427_ = v___x_1370_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_k_1217_);
lean_ctor_set(v_reuseFailAlloc_1431_, 2, v_v_1218_);
lean_ctor_set(v_reuseFailAlloc_1431_, 3, v_l_1219_);
lean_ctor_set(v_reuseFailAlloc_1431_, 4, v_l_1392_);
v___x_1427_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_nat_add(v___x_1226_, v_size_1376_);
if (lean_obj_tag(v_r_1393_) == 0)
{
lean_object* v_size_1429_; 
v_size_1429_ = lean_ctor_get(v_r_1393_, 0);
lean_inc(v_size_1429_);
v___y_1403_ = v___x_1428_;
v___y_1404_ = v___x_1427_;
v___y_1405_ = v_size_1429_;
goto v___jp_1402_;
}
else
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_unsigned_to_nat(0u);
v___y_1403_ = v___x_1428_;
v___y_1404_ = v___x_1427_;
v___y_1405_ = v___x_1430_;
goto v___jp_1402_;
}
}
}
}
}
else
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1445_; 
v___x_1440_ = lean_nat_add(v___x_1226_, v_size_1216_);
lean_dec(v_size_1216_);
v___x_1441_ = lean_nat_add(v___x_1440_, v_size_1376_);
lean_dec(v___x_1440_);
v___x_1442_ = lean_nat_add(v___x_1226_, v_size_1376_);
v___x_1443_ = lean_nat_add(v___x_1442_, v_size_1389_);
lean_dec(v___x_1442_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v_tree_1373_);
lean_ctor_set(v___x_1370_, 3, v_r_1220_);
lean_ctor_set(v___x_1370_, 2, v_v_1375_);
lean_ctor_set(v___x_1370_, 1, v_k_1374_);
lean_ctor_set(v___x_1370_, 0, v___x_1443_);
v___x_1445_ = v___x_1370_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_k_1374_);
lean_ctor_set(v_reuseFailAlloc_1449_, 2, v_v_1375_);
lean_ctor_set(v_reuseFailAlloc_1449_, 3, v_r_1220_);
lean_ctor_set(v_reuseFailAlloc_1449_, 4, v_tree_1373_);
v___x_1445_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1447_; 
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v___x_1445_);
lean_ctor_set(v___x_1386_, 0, v___x_1441_);
v___x_1447_ = v___x_1386_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_k_1217_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_v_1218_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_l_1219_);
lean_ctor_set(v_reuseFailAlloc_1448_, 4, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
}
else
{
if (lean_obj_tag(v_l_1219_) == 0)
{
lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1479_; 
lean_inc_ref(v_l_1219_);
lean_inc(v_v_1218_);
lean_inc(v_k_1217_);
lean_inc(v_size_1216_);
v_isSharedCheck_1479_ = !lean_is_exclusive(v_l_1036_);
if (v_isSharedCheck_1479_ == 0)
{
lean_object* v_unused_1480_; lean_object* v_unused_1481_; lean_object* v_unused_1482_; lean_object* v_unused_1483_; lean_object* v_unused_1484_; 
v_unused_1480_ = lean_ctor_get(v_l_1036_, 4);
lean_dec(v_unused_1480_);
v_unused_1481_ = lean_ctor_get(v_l_1036_, 3);
lean_dec(v_unused_1481_);
v_unused_1482_ = lean_ctor_get(v_l_1036_, 2);
lean_dec(v_unused_1482_);
v_unused_1483_ = lean_ctor_get(v_l_1036_, 1);
lean_dec(v_unused_1483_);
v_unused_1484_ = lean_ctor_get(v_l_1036_, 0);
lean_dec(v_unused_1484_);
v___x_1457_ = v_l_1036_;
v_isShared_1458_ = v_isSharedCheck_1479_;
goto v_resetjp_1456_;
}
else
{
lean_dec(v_l_1036_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1479_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
if (lean_obj_tag(v_r_1220_) == 0)
{
lean_object* v_k_1459_; lean_object* v_v_1460_; lean_object* v_size_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1465_; 
v_k_1459_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_k_1459_);
v_v_1460_ = lean_ctor_get(v___x_1372_, 1);
lean_inc(v_v_1460_);
lean_dec_ref(v___x_1372_);
v_size_1461_ = lean_ctor_get(v_r_1220_, 0);
v___x_1462_ = lean_nat_add(v___x_1226_, v_size_1216_);
lean_dec(v_size_1216_);
v___x_1463_ = lean_nat_add(v___x_1226_, v_size_1461_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v_tree_1373_);
lean_ctor_set(v___x_1370_, 3, v_r_1220_);
lean_ctor_set(v___x_1370_, 2, v_v_1460_);
lean_ctor_set(v___x_1370_, 1, v_k_1459_);
lean_ctor_set(v___x_1370_, 0, v___x_1463_);
v___x_1465_ = v___x_1370_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_k_1459_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_v_1460_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v_r_1220_);
lean_ctor_set(v_reuseFailAlloc_1469_, 4, v_tree_1373_);
v___x_1465_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1467_; 
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 4, v___x_1465_);
lean_ctor_set(v___x_1457_, 0, v___x_1462_);
v___x_1467_ = v___x_1457_;
goto v_reusejp_1466_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1462_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_k_1217_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_v_1218_);
lean_ctor_set(v_reuseFailAlloc_1468_, 3, v_l_1219_);
lean_ctor_set(v_reuseFailAlloc_1468_, 4, v___x_1465_);
v___x_1467_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1466_;
}
v_reusejp_1466_:
{
return v___x_1467_;
}
}
}
else
{
lean_object* v_k_1470_; lean_object* v_v_1471_; lean_object* v___x_1472_; lean_object* v___x_1474_; 
lean_dec(v_size_1216_);
v_k_1470_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_k_1470_);
v_v_1471_ = lean_ctor_get(v___x_1372_, 1);
lean_inc(v_v_1471_);
lean_dec_ref(v___x_1372_);
v___x_1472_ = lean_unsigned_to_nat(3u);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v_r_1220_);
lean_ctor_set(v___x_1370_, 3, v_r_1220_);
lean_ctor_set(v___x_1370_, 2, v_v_1471_);
lean_ctor_set(v___x_1370_, 1, v_k_1470_);
lean_ctor_set(v___x_1370_, 0, v___x_1226_);
v___x_1474_ = v___x_1370_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1478_, 1, v_k_1470_);
lean_ctor_set(v_reuseFailAlloc_1478_, 2, v_v_1471_);
lean_ctor_set(v_reuseFailAlloc_1478_, 3, v_r_1220_);
lean_ctor_set(v_reuseFailAlloc_1478_, 4, v_r_1220_);
v___x_1474_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
lean_object* v___x_1476_; 
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 4, v___x_1474_);
lean_ctor_set(v___x_1457_, 0, v___x_1472_);
v___x_1476_ = v___x_1457_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1472_);
lean_ctor_set(v_reuseFailAlloc_1477_, 1, v_k_1217_);
lean_ctor_set(v_reuseFailAlloc_1477_, 2, v_v_1218_);
lean_ctor_set(v_reuseFailAlloc_1477_, 3, v_l_1219_);
lean_ctor_set(v_reuseFailAlloc_1477_, 4, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
}
else
{
if (lean_obj_tag(v_r_1220_) == 0)
{
lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1509_; 
lean_inc(v_l_1219_);
lean_inc(v_v_1218_);
lean_inc(v_k_1217_);
v_isSharedCheck_1509_ = !lean_is_exclusive(v_l_1036_);
if (v_isSharedCheck_1509_ == 0)
{
lean_object* v_unused_1510_; lean_object* v_unused_1511_; lean_object* v_unused_1512_; lean_object* v_unused_1513_; lean_object* v_unused_1514_; 
v_unused_1510_ = lean_ctor_get(v_l_1036_, 4);
lean_dec(v_unused_1510_);
v_unused_1511_ = lean_ctor_get(v_l_1036_, 3);
lean_dec(v_unused_1511_);
v_unused_1512_ = lean_ctor_get(v_l_1036_, 2);
lean_dec(v_unused_1512_);
v_unused_1513_ = lean_ctor_get(v_l_1036_, 1);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v_l_1036_, 0);
lean_dec(v_unused_1514_);
v___x_1486_ = v_l_1036_;
v_isShared_1487_ = v_isSharedCheck_1509_;
goto v_resetjp_1485_;
}
else
{
lean_dec(v_l_1036_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1509_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_k_1488_; lean_object* v_v_1489_; lean_object* v_k_1490_; lean_object* v_v_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1505_; 
v_k_1488_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_k_1488_);
v_v_1489_ = lean_ctor_get(v___x_1372_, 1);
lean_inc(v_v_1489_);
lean_dec_ref(v___x_1372_);
v_k_1490_ = lean_ctor_get(v_r_1220_, 1);
v_v_1491_ = lean_ctor_get(v_r_1220_, 2);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_r_1220_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; lean_object* v_unused_1507_; lean_object* v_unused_1508_; 
v_unused_1506_ = lean_ctor_get(v_r_1220_, 4);
lean_dec(v_unused_1506_);
v_unused_1507_ = lean_ctor_get(v_r_1220_, 3);
lean_dec(v_unused_1507_);
v_unused_1508_ = lean_ctor_get(v_r_1220_, 0);
lean_dec(v_unused_1508_);
v___x_1493_ = v_r_1220_;
v_isShared_1494_ = v_isSharedCheck_1505_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_v_1491_);
lean_inc(v_k_1490_);
lean_dec(v_r_1220_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1505_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = lean_unsigned_to_nat(3u);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 4, v_l_1219_);
lean_ctor_set(v___x_1493_, 3, v_l_1219_);
lean_ctor_set(v___x_1493_, 2, v_v_1218_);
lean_ctor_set(v___x_1493_, 1, v_k_1217_);
lean_ctor_set(v___x_1493_, 0, v___x_1226_);
v___x_1497_ = v___x_1493_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_k_1217_);
lean_ctor_set(v_reuseFailAlloc_1504_, 2, v_v_1218_);
lean_ctor_set(v_reuseFailAlloc_1504_, 3, v_l_1219_);
lean_ctor_set(v_reuseFailAlloc_1504_, 4, v_l_1219_);
v___x_1497_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
lean_object* v___x_1499_; 
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v_l_1219_);
lean_ctor_set(v___x_1370_, 3, v_l_1219_);
lean_ctor_set(v___x_1370_, 2, v_v_1489_);
lean_ctor_set(v___x_1370_, 1, v_k_1488_);
lean_ctor_set(v___x_1370_, 0, v___x_1226_);
v___x_1499_ = v___x_1370_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1226_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v_k_1488_);
lean_ctor_set(v_reuseFailAlloc_1503_, 2, v_v_1489_);
lean_ctor_set(v_reuseFailAlloc_1503_, 3, v_l_1219_);
lean_ctor_set(v_reuseFailAlloc_1503_, 4, v_l_1219_);
v___x_1499_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1501_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 4, v___x_1499_);
lean_ctor_set(v___x_1486_, 3, v___x_1497_);
lean_ctor_set(v___x_1486_, 2, v_v_1491_);
lean_ctor_set(v___x_1486_, 1, v_k_1490_);
lean_ctor_set(v___x_1486_, 0, v___x_1495_);
v___x_1501_ = v___x_1486_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v_k_1490_);
lean_ctor_set(v_reuseFailAlloc_1502_, 2, v_v_1491_);
lean_ctor_set(v_reuseFailAlloc_1502_, 3, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1502_, 4, v___x_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
}
}
}
}
else
{
lean_object* v_k_1515_; lean_object* v_v_1516_; lean_object* v___x_1517_; lean_object* v___x_1519_; 
v_k_1515_ = lean_ctor_get(v___x_1372_, 0);
lean_inc(v_k_1515_);
v_v_1516_ = lean_ctor_get(v___x_1372_, 1);
lean_inc(v_v_1516_);
lean_dec_ref(v___x_1372_);
v___x_1517_ = lean_unsigned_to_nat(2u);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 4, v_r_1220_);
lean_ctor_set(v___x_1370_, 3, v_l_1036_);
lean_ctor_set(v___x_1370_, 2, v_v_1516_);
lean_ctor_set(v___x_1370_, 1, v_k_1515_);
lean_ctor_set(v___x_1370_, 0, v___x_1517_);
v___x_1519_ = v___x_1370_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v_k_1515_);
lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_v_1516_);
lean_ctor_set(v_reuseFailAlloc_1520_, 3, v_l_1036_);
lean_ctor_set(v_reuseFailAlloc_1520_, 4, v_r_1220_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
}
}
}
else
{
return v_l_1036_;
}
}
else
{
return v_r_1037_;
}
}
default: 
{
lean_object* v_impl_1527_; lean_object* v___x_1528_; 
v_impl_1527_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1032_, v_r_1037_);
v___x_1528_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_impl_1527_) == 0)
{
if (lean_obj_tag(v_l_1036_) == 0)
{
lean_object* v_size_1529_; lean_object* v_size_1530_; lean_object* v_k_1531_; lean_object* v_v_1532_; lean_object* v_l_1533_; lean_object* v_r_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v_size_1529_ = lean_ctor_get(v_impl_1527_, 0);
lean_inc(v_size_1529_);
v_size_1530_ = lean_ctor_get(v_l_1036_, 0);
v_k_1531_ = lean_ctor_get(v_l_1036_, 1);
v_v_1532_ = lean_ctor_get(v_l_1036_, 2);
v_l_1533_ = lean_ctor_get(v_l_1036_, 3);
v_r_1534_ = lean_ctor_get(v_l_1036_, 4);
lean_inc(v_r_1534_);
v___x_1535_ = lean_unsigned_to_nat(3u);
v___x_1536_ = lean_nat_mul(v___x_1535_, v_size_1529_);
v___x_1537_ = lean_nat_dec_lt(v___x_1536_, v_size_1530_);
lean_dec(v___x_1536_);
if (v___x_1537_ == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1541_; 
lean_dec(v_r_1534_);
v___x_1538_ = lean_nat_add(v___x_1528_, v_size_1530_);
v___x_1539_ = lean_nat_add(v___x_1538_, v_size_1529_);
lean_dec(v_size_1529_);
lean_dec(v___x_1538_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v_impl_1527_);
lean_ctor_set(v___x_1039_, 0, v___x_1539_);
v___x_1541_ = v___x_1039_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1542_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1542_, 3, v_l_1036_);
lean_ctor_set(v_reuseFailAlloc_1542_, 4, v_impl_1527_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
else
{
lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1608_; 
lean_inc(v_l_1533_);
lean_inc(v_v_1532_);
lean_inc(v_k_1531_);
lean_inc(v_size_1530_);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_l_1036_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; lean_object* v_unused_1610_; lean_object* v_unused_1611_; lean_object* v_unused_1612_; lean_object* v_unused_1613_; 
v_unused_1609_ = lean_ctor_get(v_l_1036_, 4);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_l_1036_, 3);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_l_1036_, 2);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_l_1036_, 1);
lean_dec(v_unused_1612_);
v_unused_1613_ = lean_ctor_get(v_l_1036_, 0);
lean_dec(v_unused_1613_);
v___x_1544_ = v_l_1036_;
v_isShared_1545_ = v_isSharedCheck_1608_;
goto v_resetjp_1543_;
}
else
{
lean_dec(v_l_1036_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1608_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v_size_1546_; lean_object* v_size_1547_; lean_object* v_k_1548_; lean_object* v_v_1549_; lean_object* v_l_1550_; lean_object* v_r_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v_size_1546_ = lean_ctor_get(v_l_1533_, 0);
v_size_1547_ = lean_ctor_get(v_r_1534_, 0);
v_k_1548_ = lean_ctor_get(v_r_1534_, 1);
v_v_1549_ = lean_ctor_get(v_r_1534_, 2);
v_l_1550_ = lean_ctor_get(v_r_1534_, 3);
v_r_1551_ = lean_ctor_get(v_r_1534_, 4);
v___x_1552_ = lean_unsigned_to_nat(2u);
v___x_1553_ = lean_nat_mul(v___x_1552_, v_size_1546_);
v___x_1554_ = lean_nat_dec_lt(v_size_1547_, v___x_1553_);
lean_dec(v___x_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1583_; 
lean_inc(v_r_1551_);
lean_inc(v_l_1550_);
lean_inc(v_v_1549_);
lean_inc(v_k_1548_);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_r_1534_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; lean_object* v_unused_1585_; lean_object* v_unused_1586_; lean_object* v_unused_1587_; lean_object* v_unused_1588_; 
v_unused_1584_ = lean_ctor_get(v_r_1534_, 4);
lean_dec(v_unused_1584_);
v_unused_1585_ = lean_ctor_get(v_r_1534_, 3);
lean_dec(v_unused_1585_);
v_unused_1586_ = lean_ctor_get(v_r_1534_, 2);
lean_dec(v_unused_1586_);
v_unused_1587_ = lean_ctor_get(v_r_1534_, 1);
lean_dec(v_unused_1587_);
v_unused_1588_ = lean_ctor_get(v_r_1534_, 0);
lean_dec(v_unused_1588_);
v___x_1556_ = v_r_1534_;
v_isShared_1557_ = v_isSharedCheck_1583_;
goto v_resetjp_1555_;
}
else
{
lean_dec(v_r_1534_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1583_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___y_1561_; lean_object* v___y_1562_; lean_object* v___y_1563_; lean_object* v___x_1571_; lean_object* v___y_1573_; 
v___x_1558_ = lean_nat_add(v___x_1528_, v_size_1530_);
lean_dec(v_size_1530_);
v___x_1559_ = lean_nat_add(v___x_1558_, v_size_1529_);
lean_dec(v___x_1558_);
v___x_1571_ = lean_nat_add(v___x_1528_, v_size_1546_);
if (lean_obj_tag(v_l_1550_) == 0)
{
lean_object* v_size_1581_; 
v_size_1581_ = lean_ctor_get(v_l_1550_, 0);
lean_inc(v_size_1581_);
v___y_1573_ = v_size_1581_;
goto v___jp_1572_;
}
else
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_unsigned_to_nat(0u);
v___y_1573_ = v___x_1582_;
goto v___jp_1572_;
}
v___jp_1560_:
{
lean_object* v___x_1564_; lean_object* v___x_1566_; 
v___x_1564_ = lean_nat_add(v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec(v___y_1562_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 4, v_impl_1527_);
lean_ctor_set(v___x_1556_, 3, v_r_1551_);
lean_ctor_set(v___x_1556_, 2, v_v_1035_);
lean_ctor_set(v___x_1556_, 1, v_k_1034_);
lean_ctor_set(v___x_1556_, 0, v___x_1564_);
v___x_1566_ = v___x_1556_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1564_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1570_, 3, v_r_1551_);
lean_ctor_set(v_reuseFailAlloc_1570_, 4, v_impl_1527_);
v___x_1566_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
lean_object* v___x_1568_; 
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 4, v___x_1566_);
lean_ctor_set(v___x_1544_, 3, v___y_1561_);
lean_ctor_set(v___x_1544_, 2, v_v_1549_);
lean_ctor_set(v___x_1544_, 1, v_k_1548_);
lean_ctor_set(v___x_1544_, 0, v___x_1559_);
v___x_1568_ = v___x_1544_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1559_);
lean_ctor_set(v_reuseFailAlloc_1569_, 1, v_k_1548_);
lean_ctor_set(v_reuseFailAlloc_1569_, 2, v_v_1549_);
lean_ctor_set(v_reuseFailAlloc_1569_, 3, v___y_1561_);
lean_ctor_set(v_reuseFailAlloc_1569_, 4, v___x_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
v___jp_1572_:
{
lean_object* v___x_1574_; lean_object* v___x_1576_; 
v___x_1574_ = lean_nat_add(v___x_1571_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec(v___x_1571_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v_l_1550_);
lean_ctor_set(v___x_1039_, 3, v_l_1533_);
lean_ctor_set(v___x_1039_, 2, v_v_1532_);
lean_ctor_set(v___x_1039_, 1, v_k_1531_);
lean_ctor_set(v___x_1039_, 0, v___x_1574_);
v___x_1576_ = v___x_1039_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1580_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1580_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1580_, 4, v_l_1550_);
v___x_1576_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_nat_add(v___x_1528_, v_size_1529_);
lean_dec(v_size_1529_);
if (lean_obj_tag(v_r_1551_) == 0)
{
lean_object* v_size_1578_; 
v_size_1578_ = lean_ctor_get(v_r_1551_, 0);
lean_inc(v_size_1578_);
v___y_1561_ = v___x_1576_;
v___y_1562_ = v___x_1577_;
v___y_1563_ = v_size_1578_;
goto v___jp_1560_;
}
else
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_unsigned_to_nat(0u);
v___y_1561_ = v___x_1576_;
v___y_1562_ = v___x_1577_;
v___y_1563_ = v___x_1579_;
goto v___jp_1560_;
}
}
}
}
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
lean_del_object(v___x_1039_);
v___x_1589_ = lean_nat_add(v___x_1528_, v_size_1530_);
lean_dec(v_size_1530_);
v___x_1590_ = lean_nat_add(v___x_1589_, v_size_1529_);
lean_dec(v___x_1589_);
v___x_1591_ = lean_nat_add(v___x_1528_, v_size_1529_);
lean_dec(v_size_1529_);
v___x_1592_ = lean_nat_add(v___x_1591_, v_size_1547_);
lean_dec(v___x_1591_);
lean_inc_ref(v_impl_1527_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 4, v_impl_1527_);
lean_ctor_set(v___x_1544_, 3, v_r_1534_);
lean_ctor_set(v___x_1544_, 2, v_v_1035_);
lean_ctor_set(v___x_1544_, 1, v_k_1034_);
lean_ctor_set(v___x_1544_, 0, v___x_1592_);
v___x_1594_ = v___x_1544_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1592_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1607_, 3, v_r_1534_);
lean_ctor_set(v_reuseFailAlloc_1607_, 4, v_impl_1527_);
v___x_1594_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
v_isSharedCheck_1601_ = !lean_is_exclusive(v_impl_1527_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; lean_object* v_unused_1603_; lean_object* v_unused_1604_; lean_object* v_unused_1605_; lean_object* v_unused_1606_; 
v_unused_1602_ = lean_ctor_get(v_impl_1527_, 4);
lean_dec(v_unused_1602_);
v_unused_1603_ = lean_ctor_get(v_impl_1527_, 3);
lean_dec(v_unused_1603_);
v_unused_1604_ = lean_ctor_get(v_impl_1527_, 2);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v_impl_1527_, 1);
lean_dec(v_unused_1605_);
v_unused_1606_ = lean_ctor_get(v_impl_1527_, 0);
lean_dec(v_unused_1606_);
v___x_1596_ = v_impl_1527_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_dec(v_impl_1527_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 4, v___x_1594_);
lean_ctor_set(v___x_1596_, 3, v_l_1533_);
lean_ctor_set(v___x_1596_, 2, v_v_1532_);
lean_ctor_set(v___x_1596_, 1, v_k_1531_);
lean_ctor_set(v___x_1596_, 0, v___x_1590_);
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_k_1531_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_v_1532_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v_l_1533_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v___x_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
}
}
else
{
lean_object* v_size_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
v_size_1614_ = lean_ctor_get(v_impl_1527_, 0);
lean_inc(v_size_1614_);
v___x_1615_ = lean_nat_add(v___x_1528_, v_size_1614_);
lean_dec(v_size_1614_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v_impl_1527_);
lean_ctor_set(v___x_1039_, 0, v___x_1615_);
v___x_1617_ = v___x_1039_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1618_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1618_, 3, v_l_1036_);
lean_ctor_set(v_reuseFailAlloc_1618_, 4, v_impl_1527_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
else
{
if (lean_obj_tag(v_l_1036_) == 0)
{
lean_object* v_l_1619_; 
v_l_1619_ = lean_ctor_get(v_l_1036_, 3);
if (lean_obj_tag(v_l_1619_) == 0)
{
lean_object* v_r_1620_; 
lean_inc_ref(v_l_1619_);
v_r_1620_ = lean_ctor_get(v_l_1036_, 4);
lean_inc(v_r_1620_);
if (lean_obj_tag(v_r_1620_) == 0)
{
lean_object* v_size_1621_; lean_object* v_k_1622_; lean_object* v_v_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1636_; 
v_size_1621_ = lean_ctor_get(v_l_1036_, 0);
v_k_1622_ = lean_ctor_get(v_l_1036_, 1);
v_v_1623_ = lean_ctor_get(v_l_1036_, 2);
v_isSharedCheck_1636_ = !lean_is_exclusive(v_l_1036_);
if (v_isSharedCheck_1636_ == 0)
{
lean_object* v_unused_1637_; lean_object* v_unused_1638_; 
v_unused_1637_ = lean_ctor_get(v_l_1036_, 4);
lean_dec(v_unused_1637_);
v_unused_1638_ = lean_ctor_get(v_l_1036_, 3);
lean_dec(v_unused_1638_);
v___x_1625_ = v_l_1036_;
v_isShared_1626_ = v_isSharedCheck_1636_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_v_1623_);
lean_inc(v_k_1622_);
lean_inc(v_size_1621_);
lean_dec(v_l_1036_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1636_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v_size_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
v_size_1627_ = lean_ctor_get(v_r_1620_, 0);
v___x_1628_ = lean_nat_add(v___x_1528_, v_size_1621_);
lean_dec(v_size_1621_);
v___x_1629_ = lean_nat_add(v___x_1528_, v_size_1627_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 4, v_impl_1527_);
lean_ctor_set(v___x_1625_, 3, v_r_1620_);
lean_ctor_set(v___x_1625_, 2, v_v_1035_);
lean_ctor_set(v___x_1625_, 1, v_k_1034_);
lean_ctor_set(v___x_1625_, 0, v___x_1629_);
v___x_1631_ = v___x_1625_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1629_);
lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1635_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1635_, 3, v_r_1620_);
lean_ctor_set(v_reuseFailAlloc_1635_, 4, v_impl_1527_);
v___x_1631_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
lean_object* v___x_1633_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v___x_1631_);
lean_ctor_set(v___x_1039_, 3, v_l_1619_);
lean_ctor_set(v___x_1039_, 2, v_v_1623_);
lean_ctor_set(v___x_1039_, 1, v_k_1622_);
lean_ctor_set(v___x_1039_, 0, v___x_1628_);
v___x_1633_ = v___x_1039_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_k_1622_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v_v_1623_);
lean_ctor_set(v_reuseFailAlloc_1634_, 3, v_l_1619_);
lean_ctor_set(v_reuseFailAlloc_1634_, 4, v___x_1631_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
else
{
lean_object* v_k_1639_; lean_object* v_v_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1651_; 
v_k_1639_ = lean_ctor_get(v_l_1036_, 1);
v_v_1640_ = lean_ctor_get(v_l_1036_, 2);
v_isSharedCheck_1651_ = !lean_is_exclusive(v_l_1036_);
if (v_isSharedCheck_1651_ == 0)
{
lean_object* v_unused_1652_; lean_object* v_unused_1653_; lean_object* v_unused_1654_; 
v_unused_1652_ = lean_ctor_get(v_l_1036_, 4);
lean_dec(v_unused_1652_);
v_unused_1653_ = lean_ctor_get(v_l_1036_, 3);
lean_dec(v_unused_1653_);
v_unused_1654_ = lean_ctor_get(v_l_1036_, 0);
lean_dec(v_unused_1654_);
v___x_1642_ = v_l_1036_;
v_isShared_1643_ = v_isSharedCheck_1651_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_v_1640_);
lean_inc(v_k_1639_);
lean_dec(v_l_1036_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1651_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1644_ = lean_unsigned_to_nat(3u);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 3, v_r_1620_);
lean_ctor_set(v___x_1642_, 2, v_v_1035_);
lean_ctor_set(v___x_1642_, 1, v_k_1034_);
lean_ctor_set(v___x_1642_, 0, v___x_1528_);
v___x_1646_ = v___x_1642_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1650_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1650_, 3, v_r_1620_);
lean_ctor_set(v_reuseFailAlloc_1650_, 4, v_r_1620_);
v___x_1646_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
lean_object* v___x_1648_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v___x_1646_);
lean_ctor_set(v___x_1039_, 3, v_l_1619_);
lean_ctor_set(v___x_1039_, 2, v_v_1640_);
lean_ctor_set(v___x_1039_, 1, v_k_1639_);
lean_ctor_set(v___x_1039_, 0, v___x_1644_);
v___x_1648_ = v___x_1039_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1644_);
lean_ctor_set(v_reuseFailAlloc_1649_, 1, v_k_1639_);
lean_ctor_set(v_reuseFailAlloc_1649_, 2, v_v_1640_);
lean_ctor_set(v_reuseFailAlloc_1649_, 3, v_l_1619_);
lean_ctor_set(v_reuseFailAlloc_1649_, 4, v___x_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
}
else
{
lean_object* v_r_1655_; 
v_r_1655_ = lean_ctor_get(v_l_1036_, 4);
lean_inc(v_r_1655_);
if (lean_obj_tag(v_r_1655_) == 0)
{
lean_object* v_k_1656_; lean_object* v_v_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1680_; 
lean_inc(v_l_1619_);
v_k_1656_ = lean_ctor_get(v_l_1036_, 1);
v_v_1657_ = lean_ctor_get(v_l_1036_, 2);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_l_1036_);
if (v_isSharedCheck_1680_ == 0)
{
lean_object* v_unused_1681_; lean_object* v_unused_1682_; lean_object* v_unused_1683_; 
v_unused_1681_ = lean_ctor_get(v_l_1036_, 4);
lean_dec(v_unused_1681_);
v_unused_1682_ = lean_ctor_get(v_l_1036_, 3);
lean_dec(v_unused_1682_);
v_unused_1683_ = lean_ctor_get(v_l_1036_, 0);
lean_dec(v_unused_1683_);
v___x_1659_ = v_l_1036_;
v_isShared_1660_ = v_isSharedCheck_1680_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_v_1657_);
lean_inc(v_k_1656_);
lean_dec(v_l_1036_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1680_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v_k_1661_; lean_object* v_v_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1676_; 
v_k_1661_ = lean_ctor_get(v_r_1655_, 1);
v_v_1662_ = lean_ctor_get(v_r_1655_, 2);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_r_1655_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; lean_object* v_unused_1678_; lean_object* v_unused_1679_; 
v_unused_1677_ = lean_ctor_get(v_r_1655_, 4);
lean_dec(v_unused_1677_);
v_unused_1678_ = lean_ctor_get(v_r_1655_, 3);
lean_dec(v_unused_1678_);
v_unused_1679_ = lean_ctor_get(v_r_1655_, 0);
lean_dec(v_unused_1679_);
v___x_1664_ = v_r_1655_;
v_isShared_1665_ = v_isSharedCheck_1676_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_v_1662_);
lean_inc(v_k_1661_);
lean_dec(v_r_1655_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1676_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1666_ = lean_unsigned_to_nat(3u);
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 4, v_l_1619_);
lean_ctor_set(v___x_1664_, 3, v_l_1619_);
lean_ctor_set(v___x_1664_, 2, v_v_1657_);
lean_ctor_set(v___x_1664_, 1, v_k_1656_);
lean_ctor_set(v___x_1664_, 0, v___x_1528_);
v___x_1668_ = v___x_1664_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_k_1656_);
lean_ctor_set(v_reuseFailAlloc_1675_, 2, v_v_1657_);
lean_ctor_set(v_reuseFailAlloc_1675_, 3, v_l_1619_);
lean_ctor_set(v_reuseFailAlloc_1675_, 4, v_l_1619_);
v___x_1668_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1670_; 
if (v_isShared_1660_ == 0)
{
lean_ctor_set(v___x_1659_, 4, v_l_1619_);
lean_ctor_set(v___x_1659_, 2, v_v_1035_);
lean_ctor_set(v___x_1659_, 1, v_k_1034_);
lean_ctor_set(v___x_1659_, 0, v___x_1528_);
v___x_1670_ = v___x_1659_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1674_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1674_, 3, v_l_1619_);
lean_ctor_set(v_reuseFailAlloc_1674_, 4, v_l_1619_);
v___x_1670_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v___x_1670_);
lean_ctor_set(v___x_1039_, 3, v___x_1668_);
lean_ctor_set(v___x_1039_, 2, v_v_1662_);
lean_ctor_set(v___x_1039_, 1, v_k_1661_);
lean_ctor_set(v___x_1039_, 0, v___x_1666_);
v___x_1672_ = v___x_1039_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1666_);
lean_ctor_set(v_reuseFailAlloc_1673_, 1, v_k_1661_);
lean_ctor_set(v_reuseFailAlloc_1673_, 2, v_v_1662_);
lean_ctor_set(v_reuseFailAlloc_1673_, 3, v___x_1668_);
lean_ctor_set(v_reuseFailAlloc_1673_, 4, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
}
}
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1684_ = lean_unsigned_to_nat(2u);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v_r_1655_);
lean_ctor_set(v___x_1039_, 0, v___x_1684_);
v___x_1686_ = v___x_1039_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1687_, 3, v_l_1036_);
lean_ctor_set(v_reuseFailAlloc_1687_, 4, v_r_1655_);
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
else
{
lean_object* v___x_1689_; 
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 4, v_l_1036_);
lean_ctor_set(v___x_1039_, 0, v___x_1528_);
v___x_1689_ = v___x_1039_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1690_, 1, v_k_1034_);
lean_ctor_set(v_reuseFailAlloc_1690_, 2, v_v_1035_);
lean_ctor_set(v_reuseFailAlloc_1690_, 3, v_l_1036_);
lean_ctor_set(v_reuseFailAlloc_1690_, 4, v_l_1036_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
}
}
else
{
return v_t_1033_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg___boxed(lean_object* v_k_1693_, lean_object* v_t_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1693_, v_t_1694_);
lean_dec(v_k_1693_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(lean_object* v_ext_1696_, lean_object* v_declName_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v___x_1701_; lean_object* v_ext_1702_; lean_object* v_toEnvExtension_1703_; lean_object* v_env_1704_; lean_object* v_asyncMode_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___y_1709_; lean_object* v_funCC_1735_; uint8_t v___x_1736_; 
v___x_1701_ = lean_st_ref_get(v_a_1699_);
v_ext_1702_ = lean_ctor_get(v_ext_1696_, 1);
v_toEnvExtension_1703_ = lean_ctor_get(v_ext_1702_, 0);
v_env_1704_ = lean_ctor_get(v___x_1701_, 0);
lean_inc_ref(v_env_1704_);
lean_dec(v___x_1701_);
v_asyncMode_1705_ = lean_ctor_get(v_toEnvExtension_1703_, 2);
v___x_1706_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1707_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1706_, v_ext_1696_, v_env_1704_, v_asyncMode_1705_);
v_funCC_1735_ = lean_ctor_get(v___x_1707_, 2);
lean_inc(v_funCC_1735_);
v___x_1736_ = l_Lean_NameSet_contains(v_funCC_1735_, v_declName_1697_);
lean_dec(v_funCC_1735_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; 
lean_inc(v_declName_1697_);
v___x_1737_ = l_Lean_Meta_Grind_throwNotMarkedWithGrindAttribute___redArg(v_declName_1697_, v_a_1698_, v_a_1699_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_dec_ref(v___x_1737_);
v___y_1709_ = v_a_1699_;
goto v___jp_1708_;
}
else
{
lean_dec(v___x_1707_);
lean_dec(v_declName_1697_);
lean_dec_ref(v_ext_1696_);
return v___x_1737_;
}
}
else
{
v___y_1709_ = v_a_1699_;
goto v___jp_1708_;
}
v___jp_1708_:
{
lean_object* v_funCC_1710_; lean_object* v___x_1711_; lean_object* v_env_1712_; lean_object* v_nextMacroScope_1713_; lean_object* v_ngen_1714_; lean_object* v_auxDeclNGen_1715_; lean_object* v_traceState_1716_; lean_object* v_messages_1717_; lean_object* v_infoState_1718_; lean_object* v_snapshotTasks_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1733_; 
v_funCC_1710_ = lean_ctor_get(v___x_1707_, 2);
lean_inc(v_funCC_1710_);
lean_dec(v___x_1707_);
v___x_1711_ = lean_st_ref_take(v___y_1709_);
v_env_1712_ = lean_ctor_get(v___x_1711_, 0);
v_nextMacroScope_1713_ = lean_ctor_get(v___x_1711_, 1);
v_ngen_1714_ = lean_ctor_get(v___x_1711_, 2);
v_auxDeclNGen_1715_ = lean_ctor_get(v___x_1711_, 3);
v_traceState_1716_ = lean_ctor_get(v___x_1711_, 4);
v_messages_1717_ = lean_ctor_get(v___x_1711_, 6);
v_infoState_1718_ = lean_ctor_get(v___x_1711_, 7);
v_snapshotTasks_1719_ = lean_ctor_get(v___x_1711_, 8);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1711_);
if (v_isSharedCheck_1733_ == 0)
{
lean_object* v_unused_1734_; 
v_unused_1734_ = lean_ctor_get(v___x_1711_, 5);
lean_dec(v_unused_1734_);
v___x_1721_ = v___x_1711_;
v_isShared_1722_ = v_isSharedCheck_1733_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_snapshotTasks_1719_);
lean_inc(v_infoState_1718_);
lean_inc(v_messages_1717_);
lean_inc(v_traceState_1716_);
lean_inc(v_auxDeclNGen_1715_);
lean_inc(v_ngen_1714_);
lean_inc(v_nextMacroScope_1713_);
lean_inc(v_env_1712_);
lean_dec(v___x_1711_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1733_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1723_; lean_object* v___f_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1723_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_declName_1697_, v_funCC_1710_);
lean_dec(v_declName_1697_);
v___f_1724_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___lam__0), 2, 1);
lean_closure_set(v___f_1724_, 0, v___x_1723_);
v___x_1725_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1696_, v_env_1712_, v___f_1724_);
v___x_1726_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 5, v___x_1726_);
lean_ctor_set(v___x_1721_, 0, v___x_1725_);
v___x_1728_ = v___x_1721_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_nextMacroScope_1713_);
lean_ctor_set(v_reuseFailAlloc_1732_, 2, v_ngen_1714_);
lean_ctor_set(v_reuseFailAlloc_1732_, 3, v_auxDeclNGen_1715_);
lean_ctor_set(v_reuseFailAlloc_1732_, 4, v_traceState_1716_);
lean_ctor_set(v_reuseFailAlloc_1732_, 5, v___x_1726_);
lean_ctor_set(v_reuseFailAlloc_1732_, 6, v_messages_1717_);
lean_ctor_set(v_reuseFailAlloc_1732_, 7, v_infoState_1718_);
lean_ctor_set(v_reuseFailAlloc_1732_, 8, v_snapshotTasks_1719_);
v___x_1728_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = lean_st_ref_set(v___y_1709_, v___x_1728_);
v___x_1730_ = lean_box(0);
v___x_1731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1731_, 0, v___x_1730_);
return v___x_1731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr___boxed(lean_object* v_ext_1738_, lean_object* v_declName_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v_res_1743_; 
v_res_1743_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_1738_, v_declName_1739_, v_a_1740_, v_a_1741_);
lean_dec(v_a_1741_);
lean_dec_ref(v_a_1740_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(lean_object* v_00_u03b2_1744_, lean_object* v_k_1745_, lean_object* v_t_1746_, lean_object* v_h_1747_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___redArg(v_k_1745_, v_t_1746_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0___boxed(lean_object* v_00_u03b2_1749_, lean_object* v_k_1750_, lean_object* v_t_1751_, lean_object* v_h_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr_spec__0(v_00_u03b2_1749_, v_k_1750_, v_t_1751_, v_h_1752_);
lean_dec(v_k_1750_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0(lean_object* v_a_1754_, lean_object* v_s_1755_){
_start:
{
lean_object* v_casesTypes_1756_; lean_object* v_extThms_1757_; lean_object* v_funCC_1758_; lean_object* v_inj_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
v_casesTypes_1756_ = lean_ctor_get(v_s_1755_, 0);
v_extThms_1757_ = lean_ctor_get(v_s_1755_, 1);
v_funCC_1758_ = lean_ctor_get(v_s_1755_, 2);
v_inj_1759_ = lean_ctor_get(v_s_1755_, 4);
v_isSharedCheck_1766_ = !lean_is_exclusive(v_s_1755_);
if (v_isSharedCheck_1766_ == 0)
{
lean_object* v_unused_1767_; 
v_unused_1767_ = lean_ctor_get(v_s_1755_, 3);
lean_dec(v_unused_1767_);
v___x_1761_ = v_s_1755_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_inj_1759_);
lean_inc(v_funCC_1758_);
lean_inc(v_extThms_1757_);
lean_inc(v_casesTypes_1756_);
lean_dec(v_s_1755_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 3, v_a_1754_);
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_casesTypes_1756_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_extThms_1757_);
lean_ctor_set(v_reuseFailAlloc_1765_, 2, v_funCC_1758_);
lean_ctor_set(v_reuseFailAlloc_1765_, 3, v_a_1754_);
lean_ctor_set(v_reuseFailAlloc_1765_, 4, v_inj_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1768_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__1);
v___x_1769_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1769_, 0, v___x_1768_);
lean_ctor_set(v___x_1769_, 1, v___x_1768_);
lean_ctor_set(v___x_1769_, 2, v___x_1768_);
lean_ctor_set(v___x_1769_, 3, v___x_1768_);
lean_ctor_set(v___x_1769_, 4, v___x_1768_);
lean_ctor_set(v___x_1769_, 5, v___x_1768_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(lean_object* v_ext_1770_, lean_object* v_declName_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_, lean_object* v_a_1775_){
_start:
{
lean_object* v___x_1777_; lean_object* v_ext_1778_; lean_object* v_toEnvExtension_1779_; lean_object* v_env_1780_; lean_object* v_asyncMode_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v_ematch_1784_; lean_object* v___x_1785_; 
v___x_1777_ = lean_st_ref_get(v_a_1775_);
v_ext_1778_ = lean_ctor_get(v_ext_1770_, 1);
v_toEnvExtension_1779_ = lean_ctor_get(v_ext_1778_, 0);
v_env_1780_ = lean_ctor_get(v___x_1777_, 0);
lean_inc_ref(v_env_1780_);
lean_dec(v___x_1777_);
v_asyncMode_1781_ = lean_ctor_get(v_toEnvExtension_1779_, 2);
v___x_1782_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1783_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1782_, v_ext_1770_, v_env_1780_, v_asyncMode_1781_);
v_ematch_1784_ = lean_ctor_get(v___x_1783_, 3);
lean_inc_ref(v_ematch_1784_);
lean_dec(v___x_1783_);
lean_inc(v_a_1775_);
lean_inc(v_a_1773_);
v___x_1785_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_ematch_1784_, v_declName_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1830_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1788_ = v___x_1785_;
v_isShared_1789_ = v_isSharedCheck_1830_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1785_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1830_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1790_; lean_object* v_env_1791_; lean_object* v_nextMacroScope_1792_; lean_object* v_ngen_1793_; lean_object* v_auxDeclNGen_1794_; lean_object* v_traceState_1795_; lean_object* v_messages_1796_; lean_object* v_infoState_1797_; lean_object* v_snapshotTasks_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1828_; 
v___x_1790_ = lean_st_ref_take(v_a_1775_);
v_env_1791_ = lean_ctor_get(v___x_1790_, 0);
v_nextMacroScope_1792_ = lean_ctor_get(v___x_1790_, 1);
v_ngen_1793_ = lean_ctor_get(v___x_1790_, 2);
v_auxDeclNGen_1794_ = lean_ctor_get(v___x_1790_, 3);
v_traceState_1795_ = lean_ctor_get(v___x_1790_, 4);
v_messages_1796_ = lean_ctor_get(v___x_1790_, 6);
v_infoState_1797_ = lean_ctor_get(v___x_1790_, 7);
v_snapshotTasks_1798_ = lean_ctor_get(v___x_1790_, 8);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v___x_1790_, 5);
lean_dec(v_unused_1829_);
v___x_1800_ = v___x_1790_;
v_isShared_1801_ = v_isSharedCheck_1828_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_snapshotTasks_1798_);
lean_inc(v_infoState_1797_);
lean_inc(v_messages_1796_);
lean_inc(v_traceState_1795_);
lean_inc(v_auxDeclNGen_1794_);
lean_inc(v_ngen_1793_);
lean_inc(v_nextMacroScope_1792_);
lean_inc(v_env_1791_);
lean_dec(v___x_1790_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1828_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___f_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___f_1802_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___lam__0), 2, 1);
lean_closure_set(v___f_1802_, 0, v_a_1786_);
v___x_1803_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1770_, v_env_1791_, v___f_1802_);
v___x_1804_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 5, v___x_1804_);
lean_ctor_set(v___x_1800_, 0, v___x_1803_);
v___x_1806_ = v___x_1800_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1803_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_nextMacroScope_1792_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_ngen_1793_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v_auxDeclNGen_1794_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_traceState_1795_);
lean_ctor_set(v_reuseFailAlloc_1827_, 5, v___x_1804_);
lean_ctor_set(v_reuseFailAlloc_1827_, 6, v_messages_1796_);
lean_ctor_set(v_reuseFailAlloc_1827_, 7, v_infoState_1797_);
lean_ctor_set(v_reuseFailAlloc_1827_, 8, v_snapshotTasks_1798_);
v___x_1806_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v_mctx_1809_; lean_object* v_zetaDeltaFVarIds_1810_; lean_object* v_postponed_1811_; lean_object* v_diag_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1825_; 
v___x_1807_ = lean_st_ref_set(v_a_1775_, v___x_1806_);
lean_dec(v_a_1775_);
v___x_1808_ = lean_st_ref_take(v_a_1773_);
v_mctx_1809_ = lean_ctor_get(v___x_1808_, 0);
v_zetaDeltaFVarIds_1810_ = lean_ctor_get(v___x_1808_, 2);
v_postponed_1811_ = lean_ctor_get(v___x_1808_, 3);
v_diag_1812_ = lean_ctor_get(v___x_1808_, 4);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1825_ == 0)
{
lean_object* v_unused_1826_; 
v_unused_1826_ = lean_ctor_get(v___x_1808_, 1);
lean_dec(v_unused_1826_);
v___x_1814_ = v___x_1808_;
v_isShared_1815_ = v_isSharedCheck_1825_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_diag_1812_);
lean_inc(v_postponed_1811_);
lean_inc(v_zetaDeltaFVarIds_1810_);
lean_inc(v_mctx_1809_);
lean_dec(v___x_1808_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1825_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1816_; lean_object* v___x_1818_; 
v___x_1816_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 1, v___x_1816_);
v___x_1818_ = v___x_1814_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_mctx_1809_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v___x_1816_);
lean_ctor_set(v_reuseFailAlloc_1824_, 2, v_zetaDeltaFVarIds_1810_);
lean_ctor_set(v_reuseFailAlloc_1824_, 3, v_postponed_1811_);
lean_ctor_set(v_reuseFailAlloc_1824_, 4, v_diag_1812_);
v___x_1818_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1822_; 
v___x_1819_ = lean_st_ref_set(v_a_1773_, v___x_1818_);
lean_dec(v_a_1773_);
v___x_1820_ = lean_box(0);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1820_);
v___x_1822_ = v___x_1788_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec(v_a_1775_);
lean_dec(v_a_1773_);
lean_dec_ref(v_ext_1770_);
v_a_1831_ = lean_ctor_get(v___x_1785_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1785_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1785_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1785_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___boxed(lean_object* v_ext_1839_, lean_object* v_declName_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr(v_ext_1839_, v_declName_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0(lean_object* v_a_1847_, lean_object* v_s_1848_){
_start:
{
lean_object* v_casesTypes_1849_; lean_object* v_extThms_1850_; lean_object* v_funCC_1851_; lean_object* v_ematch_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
v_casesTypes_1849_ = lean_ctor_get(v_s_1848_, 0);
v_extThms_1850_ = lean_ctor_get(v_s_1848_, 1);
v_funCC_1851_ = lean_ctor_get(v_s_1848_, 2);
v_ematch_1852_ = lean_ctor_get(v_s_1848_, 3);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_s_1848_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; 
v_unused_1860_ = lean_ctor_get(v_s_1848_, 4);
lean_dec(v_unused_1860_);
v___x_1854_ = v_s_1848_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_ematch_1852_);
lean_inc(v_funCC_1851_);
lean_inc(v_extThms_1850_);
lean_inc(v_casesTypes_1849_);
lean_dec(v_s_1848_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 4, v_a_1847_);
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_casesTypes_1849_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_extThms_1850_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_funCC_1851_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_ematch_1852_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_a_1847_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr(lean_object* v_ext_1861_, lean_object* v_declName_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_){
_start:
{
lean_object* v___x_1868_; lean_object* v_ext_1869_; lean_object* v_toEnvExtension_1870_; lean_object* v_env_1871_; lean_object* v_asyncMode_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v_inj_1875_; lean_object* v___x_1876_; 
v___x_1868_ = lean_st_ref_get(v_a_1866_);
v_ext_1869_ = lean_ctor_get(v_ext_1861_, 1);
v_toEnvExtension_1870_ = lean_ctor_get(v_ext_1869_, 0);
v_env_1871_ = lean_ctor_get(v___x_1868_, 0);
lean_inc_ref(v_env_1871_);
lean_dec(v___x_1868_);
v_asyncMode_1872_ = lean_ctor_get(v_toEnvExtension_1870_, 2);
v___x_1873_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_1874_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_1873_, v_ext_1861_, v_env_1871_, v_asyncMode_1872_);
v_inj_1875_ = lean_ctor_get(v___x_1874_, 4);
lean_inc_ref(v_inj_1875_);
lean_dec(v___x_1874_);
lean_inc(v_a_1866_);
lean_inc(v_a_1864_);
v___x_1876_ = l_Lean_Meta_Grind_Theorems_eraseDecl___redArg(v_inj_1875_, v_declName_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1921_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1879_ = v___x_1876_;
v_isShared_1880_ = v_isSharedCheck_1921_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v___x_1876_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1921_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; lean_object* v_env_1882_; lean_object* v_nextMacroScope_1883_; lean_object* v_ngen_1884_; lean_object* v_auxDeclNGen_1885_; lean_object* v_traceState_1886_; lean_object* v_messages_1887_; lean_object* v_infoState_1888_; lean_object* v_snapshotTasks_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1919_; 
v___x_1881_ = lean_st_ref_take(v_a_1866_);
v_env_1882_ = lean_ctor_get(v___x_1881_, 0);
v_nextMacroScope_1883_ = lean_ctor_get(v___x_1881_, 1);
v_ngen_1884_ = lean_ctor_get(v___x_1881_, 2);
v_auxDeclNGen_1885_ = lean_ctor_get(v___x_1881_, 3);
v_traceState_1886_ = lean_ctor_get(v___x_1881_, 4);
v_messages_1887_ = lean_ctor_get(v___x_1881_, 6);
v_infoState_1888_ = lean_ctor_get(v___x_1881_, 7);
v_snapshotTasks_1889_ = lean_ctor_get(v___x_1881_, 8);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1919_ == 0)
{
lean_object* v_unused_1920_; 
v_unused_1920_ = lean_ctor_get(v___x_1881_, 5);
lean_dec(v_unused_1920_);
v___x_1891_ = v___x_1881_;
v_isShared_1892_ = v_isSharedCheck_1919_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_snapshotTasks_1889_);
lean_inc(v_infoState_1888_);
lean_inc(v_messages_1887_);
lean_inc(v_traceState_1886_);
lean_inc(v_auxDeclNGen_1885_);
lean_inc(v_ngen_1884_);
lean_inc(v_nextMacroScope_1883_);
lean_inc(v_env_1882_);
lean_dec(v___x_1881_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1919_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___f_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___f_1893_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseInjectiveAttr___lam__0), 2, 1);
lean_closure_set(v___f_1893_, 0, v_a_1877_);
v___x_1894_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v_ext_1861_, v_env_1882_, v___f_1893_);
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
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1894_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_nextMacroScope_1883_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_ngen_1884_);
lean_ctor_set(v_reuseFailAlloc_1918_, 3, v_auxDeclNGen_1885_);
lean_ctor_set(v_reuseFailAlloc_1918_, 4, v_traceState_1886_);
lean_ctor_set(v_reuseFailAlloc_1918_, 5, v___x_1895_);
lean_ctor_set(v_reuseFailAlloc_1918_, 6, v_messages_1887_);
lean_ctor_set(v_reuseFailAlloc_1918_, 7, v_infoState_1888_);
lean_ctor_set(v_reuseFailAlloc_1918_, 8, v_snapshotTasks_1889_);
v___x_1897_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v_mctx_1900_; lean_object* v_zetaDeltaFVarIds_1901_; lean_object* v_postponed_1902_; lean_object* v_diag_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1916_; 
v___x_1898_ = lean_st_ref_set(v_a_1866_, v___x_1897_);
lean_dec(v_a_1866_);
v___x_1899_ = lean_st_ref_take(v_a_1864_);
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
v___x_1910_ = lean_st_ref_set(v_a_1864_, v___x_1909_);
lean_dec(v_a_1864_);
v___x_1911_ = lean_box(0);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 0, v___x_1911_);
v___x_1913_ = v___x_1879_;
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
lean_dec(v_a_1866_);
lean_dec(v_a_1864_);
lean_dec_ref(v_ext_1861_);
v_a_1922_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1876_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1876_);
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
lean_inc_ref(v_es_1962_);
lean_dec_ref(v_x_1959_);
v___x_1963_ = lean_box(2);
v___x_1964_ = ((size_t)5ULL);
v___x_1965_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1);
v___x_1966_ = lean_usize_land(v_x_1960_, v___x_1965_);
v_j_1967_ = lean_usize_to_nat(v___x_1966_);
v___x_1968_ = lean_array_get(v___x_1963_, v_es_1962_, v_j_1967_);
lean_dec(v_j_1967_);
lean_dec_ref(v_es_1962_);
switch(lean_obj_tag(v___x_1968_))
{
case 0:
{
lean_object* v_key_1969_; uint8_t v___x_1970_; 
v_key_1969_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_key_1969_);
lean_dec_ref(v___x_1968_);
v___x_1970_ = lean_name_eq(v_x_1961_, v_key_1969_);
lean_dec(v_key_1969_);
return v___x_1970_;
}
case 1:
{
lean_object* v_node_1971_; size_t v___x_1972_; 
v_node_1971_ = lean_ctor_get(v___x_1968_, 0);
lean_inc(v_node_1971_);
lean_dec_ref(v___x_1968_);
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
lean_inc_ref(v_ks_1975_);
lean_dec_ref(v_x_1959_);
v___x_1976_ = lean_unsigned_to_nat(0u);
v___x_1977_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0_spec__1___redArg(v_ks_1975_, v___x_1976_, v_x_1961_);
lean_dec_ref(v_ks_1975_);
return v___x_1977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___boxed(lean_object* v_x_1978_, lean_object* v_x_1979_, lean_object* v_x_1980_){
_start:
{
size_t v_x_456__boxed_1981_; uint8_t v_res_1982_; lean_object* v_r_1983_; 
v_x_456__boxed_1981_ = lean_unbox_usize(v_x_1979_);
lean_dec(v_x_1979_);
v_res_1982_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg(v_x_1978_, v_x_456__boxed_1981_, v_x_1980_);
lean_dec(v_x_1980_);
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
size_t v_x_562__boxed_2048_; uint8_t v_res_2049_; lean_object* v_r_2050_; 
v_x_562__boxed_2048_ = lean_unbox_usize(v_x_2046_);
lean_dec(v_x_2046_);
v_res_2049_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0(v_00_u03b2_2044_, v_x_2045_, v_x_562__boxed_2048_, v_x_2047_);
lean_dec(v_x_2047_);
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
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
v___x_2227_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseFunCCAttr(v_ext_2206_, v_declName_2205_, v___y_2210_, v___y_2211_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
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
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
v___x_2229_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseExtAttr(v_ext_2206_, v_declName_2205_, v___y_2210_, v___y_2211_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
return v___x_2229_;
}
}
else
{
lean_object* v___x_2230_; 
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
v___x_2230_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseCasesAttr(v_ext_2206_, v_declName_2205_, v___y_2210_, v___y_2211_);
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
return v___x_2230_;
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v___y_2211_);
lean_dec_ref(v___y_2210_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2294_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__0);
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
return v___x_2296_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2297_ = lean_box(1);
v___x_2298_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2299_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_2300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2299_);
lean_ctor_set(v___x_2300_, 1, v___x_2298_);
lean_ctor_set(v___x_2300_, 2, v___x_2297_);
return v___x_2300_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2303_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_2304_ = lean_unsigned_to_nat(0u);
v___x_2305_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2304_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
lean_ctor_set(v___x_2305_, 2, v___x_2304_);
lean_ctor_set(v___x_2305_, 3, v___x_2303_);
lean_ctor_set(v___x_2305_, 4, v___x_2303_);
lean_ctor_set(v___x_2305_, 5, v___x_2303_);
lean_ctor_set(v___x_2305_, 6, v___x_2303_);
lean_ctor_set(v___x_2305_, 7, v___x_2303_);
lean_ctor_set(v___x_2305_, 8, v___x_2303_);
return v___x_2305_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_2307_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2306_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
lean_ctor_set(v___x_2307_, 2, v___x_2306_);
lean_ctor_set(v___x_2307_, 3, v___x_2306_);
lean_ctor_set(v___x_2307_, 4, v___x_2306_);
lean_ctor_set(v___x_2307_, 5, v___x_2306_);
return v___x_2307_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__1);
v___x_2309_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2308_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
lean_ctor_set(v___x_2309_, 2, v___x_2308_);
lean_ctor_set(v___x_2309_, 3, v___x_2308_);
lean_ctor_set(v___x_2309_, 4, v___x_2308_);
return v___x_2309_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__7));
v___x_2312_ = l_Lean_stringToMessageData(v___x_2311_);
return v___x_2312_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__9));
v___x_2315_ = l_Lean_stringToMessageData(v___x_2314_);
return v___x_2315_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12(void){
_start:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2317_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__11));
v___x_2318_ = l_Lean_stringToMessageData(v___x_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(lean_object* v___x_2319_, lean_object* v_ext_2320_, uint8_t v_showInfo_2321_, lean_object* v_attrName_2322_, lean_object* v_declName_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
uint8_t v___x_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___y_2342_; 
v___x_2327_ = 1;
v___x_2328_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_2329_ = 0;
v___x_2330_ = lean_unsigned_to_nat(0u);
v___x_2331_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_2332_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_2333_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3));
v___x_2334_ = lean_box(0);
lean_inc(v___x_2319_);
v___x_2335_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2335_, 0, v___x_2328_);
lean_ctor_set(v___x_2335_, 1, v___x_2319_);
lean_ctor_set(v___x_2335_, 2, v___x_2332_);
lean_ctor_set(v___x_2335_, 3, v___x_2333_);
lean_ctor_set(v___x_2335_, 4, v___x_2334_);
lean_ctor_set(v___x_2335_, 5, v___x_2330_);
lean_ctor_set(v___x_2335_, 6, v___x_2334_);
lean_ctor_set_uint8(v___x_2335_, sizeof(void*)*7, v___x_2329_);
lean_ctor_set_uint8(v___x_2335_, sizeof(void*)*7 + 1, v___x_2329_);
lean_ctor_set_uint8(v___x_2335_, sizeof(void*)*7 + 2, v___x_2329_);
lean_ctor_set_uint8(v___x_2335_, sizeof(void*)*7 + 3, v___x_2327_);
v___x_2336_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_2337_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_2338_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_2339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2336_);
lean_ctor_set(v___x_2339_, 1, v___x_2337_);
lean_ctor_set(v___x_2339_, 2, v___x_2319_);
lean_ctor_set(v___x_2339_, 3, v___x_2331_);
lean_ctor_set(v___x_2339_, 4, v___x_2338_);
v___x_2340_ = lean_st_mk_ref(v___x_2339_);
if (v_showInfo_2321_ == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2353_; 
lean_dec(v_attrName_2322_);
v___x_2352_ = lean_box(0);
lean_inc(v___x_2340_);
v___x_2353_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__0(v_declName_2323_, v_ext_2320_, v___x_2352_, v___x_2335_, v___x_2340_, v___y_2324_, v___y_2325_);
v___y_2342_ = v___x_2353_;
goto v___jp_2341_;
}
else
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
lean_dec(v_declName_2323_);
lean_dec_ref(v_ext_2320_);
v___x_2354_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__8);
v___x_2355_ = l_Lean_MessageData_ofName(v_attrName_2322_);
lean_inc_ref(v___x_2355_);
v___x_2356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2354_);
lean_ctor_set(v___x_2356_, 1, v___x_2355_);
v___x_2357_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__10);
v___x_2358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2356_);
lean_ctor_set(v___x_2358_, 1, v___x_2357_);
v___x_2359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
lean_ctor_set(v___x_2359_, 1, v___x_2355_);
v___x_2360_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__12);
v___x_2361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2359_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v___x_2362_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2361_, v___x_2335_, v___x_2340_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec_ref(v___x_2335_);
v___y_2342_ = v___x_2362_;
goto v___jp_2341_;
}
v___jp_2341_:
{
if (lean_obj_tag(v___y_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2351_; 
v_a_2343_ = lean_ctor_get(v___y_2342_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___y_2342_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2345_ = v___y_2342_;
v_isShared_2346_ = v_isSharedCheck_2351_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___y_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2351_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2347_ = lean_st_ref_get(v___x_2340_);
lean_dec(v___x_2340_);
lean_dec(v___x_2347_);
if (v_isShared_2346_ == 0)
{
v___x_2349_ = v___x_2345_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2343_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
else
{
lean_dec(v___x_2340_);
return v___y_2342_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed(lean_object* v___x_2363_, lean_object* v_ext_2364_, lean_object* v_showInfo_2365_, lean_object* v_attrName_2366_, lean_object* v_declName_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
uint8_t v_showInfo_boxed_2371_; lean_object* v_res_2372_; 
v_showInfo_boxed_2371_ = lean_unbox(v_showInfo_2365_);
v_res_2372_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1(v___x_2363_, v_ext_2364_, v_showInfo_boxed_2371_, v_attrName_2366_, v_declName_2367_, v___y_2368_, v___y_2369_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(lean_object* v_ext_2375_, uint8_t v_attrKind_2376_, uint8_t v_showInfo_2377_, uint8_t v_minIndexable_2378_, lean_object* v_as_x27_2379_, lean_object* v_b_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_){
_start:
{
if (lean_obj_tag(v_as_x27_2379_) == 0)
{
lean_object* v___x_2386_; 
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec_ref(v_ext_2375_);
v___x_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2386_, 0, v_b_2380_);
return v___x_2386_;
}
else
{
lean_object* v_head_2387_; lean_object* v_tail_2388_; lean_object* v___x_2389_; 
v_head_2387_ = lean_ctor_get(v_as_x27_2379_, 0);
lean_inc(v_head_2387_);
v_tail_2388_ = lean_ctor_get(v_as_x27_2379_, 1);
lean_inc(v_tail_2388_);
lean_dec_ref(v_as_x27_2379_);
v___x_2389_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2384_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref(v___x_2389_);
v___x_2391_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___closed__0));
lean_inc(v___y_2384_);
lean_inc_ref(v___y_2383_);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc_ref(v_ext_2375_);
v___x_2392_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2375_, v_head_2387_, v_attrKind_2376_, v___x_2391_, v_a_2390_, v_showInfo_2377_, v_minIndexable_2378_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v___x_2393_; 
lean_dec_ref(v___x_2392_);
v___x_2393_ = lean_box(0);
v_as_x27_2379_ = v_tail_2388_;
v_b_2380_ = v___x_2393_;
goto _start;
}
else
{
lean_dec(v_tail_2388_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec_ref(v_ext_2375_);
return v___x_2392_;
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_dec(v_tail_2388_);
lean_dec(v_head_2387_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec_ref(v_ext_2375_);
v_a_2395_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2389_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2389_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg___boxed(lean_object* v_ext_2403_, lean_object* v_attrKind_2404_, lean_object* v_showInfo_2405_, lean_object* v_minIndexable_2406_, lean_object* v_as_x27_2407_, lean_object* v_b_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
uint8_t v_attrKind_boxed_2414_; uint8_t v_showInfo_boxed_2415_; uint8_t v_minIndexable_boxed_2416_; lean_object* v_res_2417_; 
v_attrKind_boxed_2414_ = lean_unbox(v_attrKind_2404_);
v_showInfo_boxed_2415_ = lean_unbox(v_showInfo_2405_);
v_minIndexable_boxed_2416_ = lean_unbox(v_minIndexable_2406_);
v_res_2417_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2403_, v_attrKind_boxed_2414_, v_showInfo_boxed_2415_, v_minIndexable_boxed_2416_, v_as_x27_2407_, v_b_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
return v_res_2417_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1(void){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__0));
v___x_2420_ = l_Lean_stringToMessageData(v___x_2419_);
return v___x_2420_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3(void){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___x_2422_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__2));
v___x_2423_ = l_Lean_stringToMessageData(v___x_2422_);
return v___x_2423_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5(void){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__4));
v___x_2426_ = l_Lean_stringToMessageData(v___x_2425_);
return v___x_2426_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7(void){
_start:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__6));
v___x_2429_ = l_Lean_stringToMessageData(v___x_2428_);
return v___x_2429_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__10));
v___x_2435_ = l_Lean_stringToMessageData(v___x_2434_);
return v___x_2435_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__12));
v___x_2438_ = l_Lean_stringToMessageData(v___x_2437_);
return v___x_2438_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15(void){
_start:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2440_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__14));
v___x_2441_ = l_Lean_stringToMessageData(v___x_2440_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(lean_object* v_stx_2442_, lean_object* v_ext_2443_, lean_object* v_declName_2444_, uint8_t v_attrKind_2445_, uint8_t v_showInfo_2446_, uint8_t v_minIndexable_2447_, uint8_t v___x_2448_, lean_object* v_attrName_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; lean_object* v___x_2483_; 
lean_inc_ref(v___y_2452_);
v___x_2483_ = l_Lean_Meta_Grind_getAttrKindFromOpt(v_stx_2442_, v___y_2452_, v___y_2453_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref(v___x_2483_);
switch(lean_obj_tag(v_a_2484_))
{
case 0:
{
lean_object* v_k_2485_; 
lean_dec(v_attrName_2449_);
lean_dec(v_stx_2442_);
v_k_2485_ = lean_ctor_get(v_a_2484_, 0);
lean_inc(v_k_2485_);
lean_dec_ref(v_a_2484_);
if (lean_obj_tag(v_k_2485_) == 9)
{
lean_object* v___x_2486_; 
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v_declName_2444_);
lean_dec_ref(v_ext_2443_);
v___x_2486_ = l_Lean_Meta_Grind_throwInvalidUsrModifier___redArg(v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
return v___x_2486_;
}
else
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2453_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2489_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref(v___x_2487_);
v___x_2489_ = l_Lean_Meta_Grind_Extension_addEMatchAttr(v_ext_2443_, v_declName_2444_, v_attrKind_2445_, v_k_2485_, v_a_2488_, v_showInfo_2446_, v_minIndexable_2447_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
return v___x_2489_;
}
else
{
lean_object* v_a_2490_; lean_object* v___x_2492_; uint8_t v_isShared_2493_; uint8_t v_isSharedCheck_2497_; 
lean_dec(v_k_2485_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v_declName_2444_);
lean_dec_ref(v_ext_2443_);
v_a_2490_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2497_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2497_ == 0)
{
v___x_2492_ = v___x_2487_;
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
else
{
lean_inc(v_a_2490_);
lean_dec(v___x_2487_);
v___x_2492_ = lean_box(0);
v_isShared_2493_ = v_isSharedCheck_2497_;
goto v_resetjp_2491_;
}
v_resetjp_2491_:
{
lean_object* v___x_2495_; 
if (v_isShared_2493_ == 0)
{
v___x_2495_ = v___x_2492_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_a_2490_);
v___x_2495_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
return v___x_2495_;
}
}
}
}
}
case 1:
{
uint8_t v_eager_2498_; lean_object* v___x_2499_; 
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v_attrName_2449_);
lean_dec(v_stx_2442_);
v_eager_2498_ = lean_ctor_get_uint8(v_a_2484_, 0);
lean_dec_ref(v_a_2484_);
v___x_2499_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2443_, v_declName_2444_, v_eager_2498_, v_attrKind_2445_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
return v___x_2499_;
}
case 2:
{
lean_object* v___x_2500_; 
lean_dec(v_stx_2442_);
lean_inc(v___y_2453_);
lean_inc_ref(v___y_2452_);
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
lean_inc(v_declName_2444_);
v___x_2500_ = l_Lean_Meta_Grind_isCasesAttrPredicateCandidate_x3f(v_declName_2444_, v___x_2448_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_a_2501_; 
v_a_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_a_2501_);
lean_dec_ref(v___x_2500_);
if (lean_obj_tag(v_a_2501_) == 1)
{
lean_object* v_val_2502_; lean_object* v_ctors_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
lean_dec(v_attrName_2449_);
lean_dec(v_declName_2444_);
v_val_2502_ = lean_ctor_get(v_a_2501_, 0);
lean_inc(v_val_2502_);
lean_dec_ref(v_a_2501_);
v_ctors_2503_ = lean_ctor_get(v_val_2502_, 4);
lean_inc(v_ctors_2503_);
lean_dec(v_val_2502_);
v___x_2504_ = lean_box(0);
v___x_2505_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2443_, v_attrKind_2445_, v_showInfo_2446_, v_minIndexable_2447_, v_ctors_2503_, v___x_2504_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
if (lean_obj_tag(v___x_2505_) == 0)
{
lean_object* v___x_2507_; uint8_t v_isShared_2508_; uint8_t v_isSharedCheck_2512_; 
v_isSharedCheck_2512_ = !lean_is_exclusive(v___x_2505_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; 
v_unused_2513_ = lean_ctor_get(v___x_2505_, 0);
lean_dec(v_unused_2513_);
v___x_2507_ = v___x_2505_;
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
else
{
lean_dec(v___x_2505_);
v___x_2507_ = lean_box(0);
v_isShared_2508_ = v_isSharedCheck_2512_;
goto v_resetjp_2506_;
}
v_resetjp_2506_:
{
lean_object* v___x_2510_; 
if (v_isShared_2508_ == 0)
{
lean_ctor_set(v___x_2507_, 0, v___x_2504_);
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2504_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
return v___x_2510_;
}
}
}
else
{
return v___x_2505_;
}
}
else
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
lean_dec(v_a_2501_);
lean_dec_ref(v_ext_2443_);
v___x_2514_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__3);
v___x_2515_ = l_Lean_MessageData_ofName(v_attrName_2449_);
v___x_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__5);
v___x_2518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = l_Lean_MessageData_ofConstName(v_declName_2444_, v___x_2448_);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__7);
v___x_2522_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2520_);
lean_ctor_set(v___x_2522_, 1, v___x_2521_);
v___x_2523_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2522_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
return v___x_2523_;
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v_attrName_2449_);
lean_dec(v_declName_2444_);
lean_dec_ref(v_ext_2443_);
v_a_2524_ = lean_ctor_get(v___x_2500_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2500_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2500_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
case 3:
{
lean_object* v___x_2532_; 
lean_dec(v_attrName_2449_);
lean_inc(v_declName_2444_);
v___x_2532_ = l_Lean_Meta_Grind_isCasesAttrCandidate_x3f(v_declName_2444_, v___x_2448_, v___y_2452_, v___y_2453_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref(v___x_2532_);
if (lean_obj_tag(v_a_2533_) == 1)
{
lean_object* v_val_2534_; lean_object* v___x_2535_; 
lean_dec(v_declName_2444_);
lean_dec(v_stx_2442_);
v_val_2534_ = lean_ctor_get(v_a_2533_, 0);
lean_inc(v_val_2534_);
lean_dec_ref(v_a_2533_);
lean_inc_ref(v___y_2452_);
lean_inc(v_val_2534_);
lean_inc_ref(v_ext_2443_);
v___x_2535_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr(v_ext_2443_, v_val_2534_, v___x_2448_, v_attrKind_2445_, v___y_2452_, v___y_2453_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v___x_2536_; 
lean_dec_ref(v___x_2535_);
lean_inc(v___y_2453_);
lean_inc_ref(v___y_2452_);
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
v___x_2536_ = l_Lean_Meta_isInductivePredicate_x3f(v_val_2534_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2557_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2557_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2557_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
if (lean_obj_tag(v_a_2537_) == 1)
{
lean_object* v_val_2541_; lean_object* v_ctors_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
lean_del_object(v___x_2539_);
v_val_2541_ = lean_ctor_get(v_a_2537_, 0);
lean_inc(v_val_2541_);
lean_dec_ref(v_a_2537_);
v_ctors_2542_ = lean_ctor_get(v_val_2541_, 4);
lean_inc(v_ctors_2542_);
lean_dec(v_val_2541_);
v___x_2543_ = lean_box(0);
v___x_2544_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_2443_, v_attrKind_2445_, v_showInfo_2446_, v_minIndexable_2447_, v_ctors_2542_, v___x_2543_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2551_ == 0)
{
lean_object* v_unused_2552_; 
v_unused_2552_ = lean_ctor_get(v___x_2544_, 0);
lean_dec(v_unused_2552_);
v___x_2546_ = v___x_2544_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_dec(v___x_2544_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v___x_2543_);
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v___x_2543_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
else
{
return v___x_2544_;
}
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2555_; 
lean_dec(v_a_2537_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec_ref(v_ext_2443_);
v___x_2553_ = lean_box(0);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v___x_2553_);
v___x_2555_ = v___x_2539_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec_ref(v_ext_2443_);
v_a_2558_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2536_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2536_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
else
{
lean_dec(v_val_2534_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec_ref(v_ext_2443_);
return v___x_2535_;
}
}
else
{
lean_object* v___x_2566_; 
lean_dec(v_a_2533_);
v___x_2566_ = l_Lean_Meta_Grind_getGlobalSymbolPriorities___redArg(v___y_2453_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v_a_2567_; lean_object* v___x_2568_; 
v_a_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_a_2567_);
lean_dec_ref(v___x_2566_);
v___x_2568_ = l_Lean_Meta_Grind_Extension_addEMatchAttrAndSuggest(v_ext_2443_, v_stx_2442_, v_declName_2444_, v_attrKind_2445_, v_a_2567_, v_minIndexable_2447_, v_showInfo_2446_, v___x_2448_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
return v___x_2568_;
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v_declName_2444_);
lean_dec_ref(v_ext_2443_);
lean_dec(v_stx_2442_);
v_a_2569_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2566_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2566_);
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
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v_declName_2444_);
lean_dec_ref(v_ext_2443_);
lean_dec(v_stx_2442_);
v_a_2577_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2532_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2532_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
case 4:
{
lean_object* v___x_2585_; 
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v_attrName_2449_);
lean_dec(v_stx_2442_);
v___x_2585_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addExtAttr(v_ext_2443_, v_declName_2444_, v_attrKind_2445_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
return v___x_2585_;
}
case 5:
{
lean_object* v_prio_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; 
lean_dec_ref(v_ext_2443_);
lean_dec(v_stx_2442_);
v_prio_2586_ = lean_ctor_get(v_a_2484_, 0);
lean_inc(v_prio_2586_);
lean_dec_ref(v_a_2484_);
v___x_2587_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2588_ = lean_name_eq(v_attrName_2449_, v___x_2587_);
lean_dec(v_attrName_2449_);
if (v___x_2588_ == 0)
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
lean_dec(v_prio_2586_);
lean_dec(v_declName_2444_);
v___x_2589_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__11);
v___x_2590_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2589_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
return v___x_2590_;
}
else
{
lean_object* v___x_2591_; 
v___x_2591_ = l_Lean_Meta_Grind_addSymbolPriorityAttr(v_declName_2444_, v_attrKind_2445_, v_prio_2586_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
return v___x_2591_;
}
}
case 6:
{
lean_object* v___x_2592_; 
lean_dec(v_attrName_2449_);
lean_dec(v_stx_2442_);
v___x_2592_ = l_Lean_Meta_Grind_Extension_addInjectiveAttr(v_ext_2443_, v_declName_2444_, v_attrKind_2445_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
return v___x_2592_;
}
case 7:
{
lean_object* v___x_2593_; 
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v_attrName_2449_);
lean_dec(v_stx_2442_);
v___x_2593_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addFunCCAttr(v_ext_2443_, v_declName_2444_, v_attrKind_2445_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
return v___x_2593_;
}
case 8:
{
uint8_t v_post_2594_; uint8_t v_inv_2595_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
lean_dec_ref(v_ext_2443_);
lean_dec(v_stx_2442_);
v_post_2594_ = lean_ctor_get_uint8(v_a_2484_, 0);
v_inv_2595_ = lean_ctor_get_uint8(v_a_2484_, 1);
lean_dec_ref(v_a_2484_);
v___x_2604_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2605_ = lean_name_eq(v_attrName_2449_, v___x_2604_);
lean_dec(v_attrName_2449_);
if (v___x_2605_ == 0)
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_dec(v_declName_2444_);
v___x_2606_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__13);
v___x_2607_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2606_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
return v___x_2607_;
}
else
{
v___y_2597_ = v___y_2450_;
v___y_2598_ = v___y_2451_;
v___y_2599_ = v___y_2452_;
v___y_2600_ = v___y_2453_;
goto v___jp_2596_;
}
v___jp_2596_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2601_ = l_Lean_Meta_Grind_normExt;
v___x_2602_ = lean_unsigned_to_nat(1000u);
v___x_2603_ = l_Lean_Meta_addSimpTheorem(v___x_2601_, v_declName_2444_, v_post_2594_, v_inv_2595_, v_attrKind_2445_, v___x_2602_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
return v___x_2603_;
}
}
default: 
{
lean_object* v___x_2608_; uint8_t v___x_2609_; 
lean_dec_ref(v_ext_2443_);
lean_dec(v_stx_2442_);
v___x_2608_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_2609_ = lean_name_eq(v_attrName_2449_, v___x_2608_);
lean_dec(v_attrName_2449_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
lean_dec(v_declName_2444_);
v___x_2610_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__15);
v___x_2611_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2610_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
return v___x_2611_;
}
else
{
v___y_2456_ = v___y_2450_;
v___y_2457_ = v___y_2451_;
v___y_2458_ = v___y_2452_;
v___y_2459_ = v___y_2453_;
goto v___jp_2455_;
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v_attrName_2449_);
lean_dec(v_declName_2444_);
lean_dec_ref(v_ext_2443_);
lean_dec(v_stx_2442_);
v_a_2612_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2483_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2483_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
v___jp_2455_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2460_ = l_Lean_Meta_Grind_normExt;
v___x_2461_ = lean_unsigned_to_nat(1000u);
lean_inc(v___y_2459_);
lean_inc_ref(v___y_2458_);
lean_inc(v___y_2457_);
lean_inc_ref(v___y_2456_);
v___x_2462_ = l_Lean_Meta_addDeclToUnfold(v___x_2460_, v_declName_2444_, v___x_2448_, v___x_2448_, v___x_2461_, v_attrKind_2445_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2474_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2465_ = v___x_2462_;
v_isShared_2466_ = v_isSharedCheck_2474_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2462_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2474_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
uint8_t v___x_2467_; 
v___x_2467_ = lean_unbox(v_a_2463_);
lean_dec(v_a_2463_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
lean_del_object(v___x_2465_);
v___x_2468_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__1);
v___x_2469_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v___x_2468_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
return v___x_2469_;
}
else
{
lean_object* v___x_2470_; lean_object* v___x_2472_; 
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
v___x_2470_ = lean_box(0);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v___x_2470_);
v___x_2472_ = v___x_2465_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
v_a_2475_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2462_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2462_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed(lean_object* v_stx_2620_, lean_object* v_ext_2621_, lean_object* v_declName_2622_, lean_object* v_attrKind_2623_, lean_object* v_showInfo_2624_, lean_object* v_minIndexable_2625_, lean_object* v___x_2626_, lean_object* v_attrName_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
uint8_t v_attrKind_boxed_2633_; uint8_t v_showInfo_boxed_2634_; uint8_t v_minIndexable_boxed_2635_; uint8_t v___x_15741__boxed_2636_; lean_object* v_res_2637_; 
v_attrKind_boxed_2633_ = lean_unbox(v_attrKind_2623_);
v_showInfo_boxed_2634_ = lean_unbox(v_showInfo_2624_);
v_minIndexable_boxed_2635_ = lean_unbox(v_minIndexable_2625_);
v___x_15741__boxed_2636_ = lean_unbox(v___x_2626_);
v_res_2637_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2(v_stx_2620_, v_ext_2621_, v_declName_2622_, v_attrKind_boxed_2633_, v_showInfo_boxed_2634_, v_minIndexable_boxed_2635_, v___x_15741__boxed_2636_, v_attrName_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
return v_res_2637_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg(lean_object* v_cls_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_options_2644_; uint8_t v_hasTrace_2645_; 
v_options_2644_ = lean_ctor_get(v___y_2642_, 2);
v_hasTrace_2645_ = lean_ctor_get_uint8(v_options_2644_, sizeof(void*)*1);
if (v_hasTrace_2645_ == 0)
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
lean_dec(v_cls_2641_);
v___x_2646_ = lean_box(v_hasTrace_2645_);
v___x_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
return v___x_2647_;
}
else
{
lean_object* v_inheritedTraceOptions_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v_inheritedTraceOptions_2648_ = lean_ctor_get(v___y_2642_, 13);
v___x_2649_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg___closed__1));
v___x_2650_ = l_Lean_Name_append(v___x_2649_, v_cls_2641_);
v___x_2651_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2648_, v_options_2644_, v___x_2650_);
lean_dec(v___x_2650_);
v___x_2652_ = lean_box(v___x_2651_);
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
return v___x_2653_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_cls_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg(v_cls_2654_, v___y_2655_);
lean_dec_ref(v___y_2655_);
return v_res_2657_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__11___redArg(lean_object* v_keys_2658_, lean_object* v_i_2659_, lean_object* v_k_2660_){
_start:
{
lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2661_ = lean_array_get_size(v_keys_2658_);
v___x_2662_ = lean_nat_dec_lt(v_i_2659_, v___x_2661_);
if (v___x_2662_ == 0)
{
lean_dec(v_i_2659_);
return v___x_2662_;
}
else
{
lean_object* v_k_x27_2663_; uint8_t v___x_2664_; 
v_k_x27_2663_ = lean_array_fget_borrowed(v_keys_2658_, v_i_2659_);
v___x_2664_ = l_Lean_instBEqExtraModUse_beq(v_k_2660_, v_k_x27_2663_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; lean_object* v___x_2666_; 
v___x_2665_ = lean_unsigned_to_nat(1u);
v___x_2666_ = lean_nat_add(v_i_2659_, v___x_2665_);
lean_dec(v_i_2659_);
v_i_2659_ = v___x_2666_;
goto _start;
}
else
{
lean_dec(v_i_2659_);
return v___x_2664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__11___redArg___boxed(lean_object* v_keys_2668_, lean_object* v_i_2669_, lean_object* v_k_2670_){
_start:
{
uint8_t v_res_2671_; lean_object* v_r_2672_; 
v_res_2671_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__11___redArg(v_keys_2668_, v_i_2669_, v_k_2670_);
lean_dec_ref(v_k_2670_);
lean_dec_ref(v_keys_2668_);
v_r_2672_ = lean_box(v_res_2671_);
return v_r_2672_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(lean_object* v_x_2673_, size_t v_x_2674_, lean_object* v_x_2675_){
_start:
{
if (lean_obj_tag(v_x_2673_) == 0)
{
lean_object* v_es_2676_; lean_object* v___x_2677_; size_t v___x_2678_; size_t v___x_2679_; size_t v___x_2680_; lean_object* v_j_2681_; lean_object* v___x_2682_; 
v_es_2676_ = lean_ctor_get(v_x_2673_, 0);
lean_inc_ref(v_es_2676_);
lean_dec_ref(v_x_2673_);
v___x_2677_ = lean_box(2);
v___x_2678_ = ((size_t)5ULL);
v___x_2679_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0_spec__0___redArg___closed__1);
v___x_2680_ = lean_usize_land(v_x_2674_, v___x_2679_);
v_j_2681_ = lean_usize_to_nat(v___x_2680_);
v___x_2682_ = lean_array_get(v___x_2677_, v_es_2676_, v_j_2681_);
lean_dec(v_j_2681_);
lean_dec_ref(v_es_2676_);
switch(lean_obj_tag(v___x_2682_))
{
case 0:
{
lean_object* v_key_2683_; uint8_t v___x_2684_; 
v_key_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_key_2683_);
lean_dec_ref(v___x_2682_);
v___x_2684_ = l_Lean_instBEqExtraModUse_beq(v_x_2675_, v_key_2683_);
lean_dec(v_key_2683_);
return v___x_2684_;
}
case 1:
{
lean_object* v_node_2685_; size_t v___x_2686_; 
v_node_2685_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_node_2685_);
lean_dec_ref(v___x_2682_);
v___x_2686_ = lean_usize_shift_right(v_x_2674_, v___x_2678_);
v_x_2673_ = v_node_2685_;
v_x_2674_ = v___x_2686_;
goto _start;
}
default: 
{
uint8_t v___x_2688_; 
v___x_2688_ = 0;
return v___x_2688_;
}
}
}
else
{
lean_object* v_ks_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
v_ks_2689_ = lean_ctor_get(v_x_2673_, 0);
lean_inc_ref(v_ks_2689_);
lean_dec_ref(v_x_2673_);
v___x_2690_ = lean_unsigned_to_nat(0u);
v___x_2691_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__11___redArg(v_ks_2689_, v___x_2690_, v_x_2675_);
lean_dec_ref(v_ks_2689_);
return v___x_2691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg___boxed(lean_object* v_x_2692_, lean_object* v_x_2693_, lean_object* v_x_2694_){
_start:
{
size_t v_x_16169__boxed_2695_; uint8_t v_res_2696_; lean_object* v_r_2697_; 
v_x_16169__boxed_2695_ = lean_unbox_usize(v_x_2693_);
lean_dec(v_x_2693_);
v_res_2696_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2692_, v_x_16169__boxed_2695_, v_x_2694_);
lean_dec_ref(v_x_2694_);
v_r_2697_ = lean_box(v_res_2696_);
return v_r_2697_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(lean_object* v_x_2698_, lean_object* v_x_2699_){
_start:
{
uint64_t v___x_2700_; size_t v___x_2701_; uint8_t v___x_2702_; 
v___x_2700_ = l_Lean_instHashableExtraModUse_hash(v_x_2699_);
v___x_2701_ = lean_uint64_to_usize(v___x_2700_);
v___x_2702_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_2698_, v___x_2701_, v_x_2699_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_x_2703_, lean_object* v_x_2704_){
_start:
{
uint8_t v_res_2705_; lean_object* v_r_2706_; 
v_res_2705_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_2703_, v_x_2704_);
lean_dec_ref(v_x_2704_);
v_r_2706_ = lean_box(v_res_2705_);
return v_r_2706_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_2707_; double v___x_2708_; 
v___x_2707_ = lean_unsigned_to_nat(0u);
v___x_2708_ = lean_float_of_nat(v___x_2707_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6(lean_object* v_cls_2712_, lean_object* v_msg_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v_ref_2719_; lean_object* v___x_2720_; lean_object* v_a_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2765_; 
v_ref_2719_ = lean_ctor_get(v___y_2716_, 5);
v___x_2720_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0_spec__0(v_msg_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2723_ = v___x_2720_;
v_isShared_2724_ = v_isSharedCheck_2765_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_a_2721_);
lean_dec(v___x_2720_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2765_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; lean_object* v_traceState_2726_; lean_object* v_env_2727_; lean_object* v_nextMacroScope_2728_; lean_object* v_ngen_2729_; lean_object* v_auxDeclNGen_2730_; lean_object* v_cache_2731_; lean_object* v_messages_2732_; lean_object* v_infoState_2733_; lean_object* v_snapshotTasks_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2764_; 
v___x_2725_ = lean_st_ref_take(v___y_2717_);
v_traceState_2726_ = lean_ctor_get(v___x_2725_, 4);
v_env_2727_ = lean_ctor_get(v___x_2725_, 0);
v_nextMacroScope_2728_ = lean_ctor_get(v___x_2725_, 1);
v_ngen_2729_ = lean_ctor_get(v___x_2725_, 2);
v_auxDeclNGen_2730_ = lean_ctor_get(v___x_2725_, 3);
v_cache_2731_ = lean_ctor_get(v___x_2725_, 5);
v_messages_2732_ = lean_ctor_get(v___x_2725_, 6);
v_infoState_2733_ = lean_ctor_get(v___x_2725_, 7);
v_snapshotTasks_2734_ = lean_ctor_get(v___x_2725_, 8);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2736_ = v___x_2725_;
v_isShared_2737_ = v_isSharedCheck_2764_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_snapshotTasks_2734_);
lean_inc(v_infoState_2733_);
lean_inc(v_messages_2732_);
lean_inc(v_cache_2731_);
lean_inc(v_traceState_2726_);
lean_inc(v_auxDeclNGen_2730_);
lean_inc(v_ngen_2729_);
lean_inc(v_nextMacroScope_2728_);
lean_inc(v_env_2727_);
lean_dec(v___x_2725_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2764_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
uint64_t v_tid_2738_; lean_object* v_traces_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2763_; 
v_tid_2738_ = lean_ctor_get_uint64(v_traceState_2726_, sizeof(void*)*1);
v_traces_2739_ = lean_ctor_get(v_traceState_2726_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v_traceState_2726_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2741_ = v_traceState_2726_;
v_isShared_2742_ = v_isSharedCheck_2763_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_traces_2739_);
lean_dec(v_traceState_2726_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2763_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2743_; double v___x_2744_; uint8_t v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2743_ = lean_box(0);
v___x_2744_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__0);
v___x_2745_ = 0;
v___x_2746_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__1));
v___x_2747_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2747_, 0, v_cls_2712_);
lean_ctor_set(v___x_2747_, 1, v___x_2743_);
lean_ctor_set(v___x_2747_, 2, v___x_2746_);
lean_ctor_set_float(v___x_2747_, sizeof(void*)*3, v___x_2744_);
lean_ctor_set_float(v___x_2747_, sizeof(void*)*3 + 8, v___x_2744_);
lean_ctor_set_uint8(v___x_2747_, sizeof(void*)*3 + 16, v___x_2745_);
v___x_2748_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__2));
v___x_2749_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2747_);
lean_ctor_set(v___x_2749_, 1, v_a_2721_);
lean_ctor_set(v___x_2749_, 2, v___x_2748_);
lean_inc(v_ref_2719_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v_ref_2719_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = l_Lean_PersistentArray_push___redArg(v_traces_2739_, v___x_2750_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2751_);
v___x_2753_ = v___x_2741_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2751_);
lean_ctor_set_uint64(v_reuseFailAlloc_2762_, sizeof(void*)*1, v_tid_2738_);
v___x_2753_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2755_; 
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 4, v___x_2753_);
v___x_2755_ = v___x_2736_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_env_2727_);
lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_nextMacroScope_2728_);
lean_ctor_set(v_reuseFailAlloc_2761_, 2, v_ngen_2729_);
lean_ctor_set(v_reuseFailAlloc_2761_, 3, v_auxDeclNGen_2730_);
lean_ctor_set(v_reuseFailAlloc_2761_, 4, v___x_2753_);
lean_ctor_set(v_reuseFailAlloc_2761_, 5, v_cache_2731_);
lean_ctor_set(v_reuseFailAlloc_2761_, 6, v_messages_2732_);
lean_ctor_set(v_reuseFailAlloc_2761_, 7, v_infoState_2733_);
lean_ctor_set(v_reuseFailAlloc_2761_, 8, v_snapshotTasks_2734_);
v___x_2755_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v___x_2756_ = lean_st_ref_set(v___y_2717_, v___x_2755_);
v___x_2757_ = lean_box(0);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2757_);
v___x_2759_ = v___x_2723_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___boxed(lean_object* v_cls_2766_, lean_object* v_msg_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v_res_2773_; 
v_res_2773_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6(v_cls_2766_, v_msg_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
return v_res_2773_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2(void){
_start:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2776_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__1));
v___x_2777_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__0));
v___x_2778_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_2777_, v___x_2776_);
return v___x_2778_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__5));
v___x_2784_ = l_Lean_stringToMessageData(v___x_2783_);
return v___x_2784_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8(void){
_start:
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__7));
v___x_2787_ = l_Lean_stringToMessageData(v___x_2786_);
return v___x_2787_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__1));
v___x_2789_ = l_Lean_stringToMessageData(v___x_2788_);
return v___x_2789_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__10));
v___x_2792_ = l_Lean_stringToMessageData(v___x_2791_);
return v___x_2792_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13(void){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__12));
v___x_2795_ = l_Lean_stringToMessageData(v___x_2794_);
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(lean_object* v_mod_2800_, uint8_t v_isMeta_2801_, lean_object* v_hint_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; lean_object* v_env_2809_; uint8_t v_isExporting_2810_; lean_object* v___x_2811_; lean_object* v_env_2812_; lean_object* v___x_2813_; lean_object* v_entry_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v___x_2808_ = lean_st_ref_get(v___y_2806_);
v_env_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc_ref(v_env_2809_);
lean_dec(v___x_2808_);
v_isExporting_2810_ = lean_ctor_get_uint8(v_env_2809_, sizeof(void*)*8);
lean_dec_ref(v_env_2809_);
v___x_2811_ = lean_st_ref_get(v___y_2806_);
v_env_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc_ref(v_env_2812_);
lean_dec(v___x_2811_);
v___x_2813_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_2800_);
v_entry_2814_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_2814_, 0, v_mod_2800_);
lean_ctor_set_uint8(v_entry_2814_, sizeof(void*)*1, v_isExporting_2810_);
lean_ctor_set_uint8(v_entry_2814_, sizeof(void*)*1 + 1, v_isMeta_2801_);
v___x_2815_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_2816_ = lean_box(1);
v___x_2817_ = lean_box(0);
v___x_2860_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_2813_, v___x_2815_, v_env_2812_, v___x_2816_, v___x_2817_);
v___x_2861_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_2860_, v_entry_2814_);
if (v___x_2861_ == 0)
{
lean_object* v_cls_2862_; lean_object* v___x_2863_; lean_object* v_a_2864_; lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2871_; lean_object* v___y_2872_; uint8_t v___x_2884_; 
v_cls_2862_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_2863_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg(v_cls_2862_, v___y_2805_);
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref(v___x_2863_);
v___x_2884_ = lean_unbox(v_a_2864_);
lean_dec(v_a_2864_);
if (v___x_2884_ == 0)
{
lean_dec(v_hint_2802_);
lean_dec(v_mod_2800_);
v___y_2819_ = v___y_2804_;
v___y_2820_ = v___y_2806_;
goto v___jp_2818_;
}
else
{
lean_object* v___x_2885_; lean_object* v___y_2887_; 
v___x_2885_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11);
if (v_isExporting_2810_ == 0)
{
lean_object* v___x_2894_; 
v___x_2894_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16));
v___y_2887_ = v___x_2894_;
goto v___jp_2886_;
}
else
{
lean_object* v___x_2895_; 
v___x_2895_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_2887_ = v___x_2895_;
goto v___jp_2886_;
}
v___jp_2886_:
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2888_ = l_Lean_stringToMessageData(v___y_2887_);
v___x_2889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2889_, 0, v___x_2885_);
lean_ctor_set(v___x_2889_, 1, v___x_2888_);
v___x_2890_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13);
v___x_2891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2891_, 0, v___x_2889_);
lean_ctor_set(v___x_2891_, 1, v___x_2890_);
if (v_isMeta_2801_ == 0)
{
lean_object* v___x_2892_; 
v___x_2892_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14));
v___y_2871_ = v___x_2891_;
v___y_2872_ = v___x_2892_;
goto v___jp_2870_;
}
else
{
lean_object* v___x_2893_; 
v___x_2893_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___y_2871_ = v___x_2891_;
v___y_2872_ = v___x_2893_;
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
v___x_2869_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6(v_cls_2862_, v___x_2868_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_dec_ref(v___x_2869_);
v___y_2819_ = v___y_2804_;
v___y_2820_ = v___y_2806_;
goto v___jp_2818_;
}
else
{
lean_dec_ref(v_entry_2814_);
return v___x_2869_;
}
}
v___jp_2870_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; 
v___x_2873_ = l_Lean_stringToMessageData(v___y_2872_);
v___x_2874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___y_2871_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_2876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2874_);
lean_ctor_set(v___x_2876_, 1, v___x_2875_);
v___x_2877_ = l_Lean_MessageData_ofName(v_mod_2800_);
v___x_2878_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2876_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
v___x_2879_ = l_Lean_Name_isAnonymous(v_hint_2802_);
if (v___x_2879_ == 0)
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2880_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_2881_ = l_Lean_MessageData_ofName(v_hint_2802_);
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
lean_dec(v_hint_2802_);
v___x_2883_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_2866_ = v___x_2878_;
v___y_2867_ = v___x_2883_;
goto v___jp_2865_;
}
}
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
lean_dec_ref(v_entry_2814_);
lean_dec(v_hint_2802_);
lean_dec(v_mod_2800_);
v___x_2896_ = lean_box(0);
v___x_2897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2896_);
return v___x_2897_;
}
v___jp_2818_:
{
lean_object* v___x_2821_; lean_object* v_toEnvExtension_2822_; lean_object* v_env_2823_; lean_object* v_nextMacroScope_2824_; lean_object* v_ngen_2825_; lean_object* v_auxDeclNGen_2826_; lean_object* v_traceState_2827_; lean_object* v_messages_2828_; lean_object* v_infoState_2829_; lean_object* v_snapshotTasks_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2858_; 
v___x_2821_ = lean_st_ref_take(v___y_2820_);
v_toEnvExtension_2822_ = lean_ctor_get(v___x_2815_, 0);
lean_inc_ref(v_toEnvExtension_2822_);
v_env_2823_ = lean_ctor_get(v___x_2821_, 0);
v_nextMacroScope_2824_ = lean_ctor_get(v___x_2821_, 1);
v_ngen_2825_ = lean_ctor_get(v___x_2821_, 2);
v_auxDeclNGen_2826_ = lean_ctor_get(v___x_2821_, 3);
v_traceState_2827_ = lean_ctor_get(v___x_2821_, 4);
v_messages_2828_ = lean_ctor_get(v___x_2821_, 6);
v_infoState_2829_ = lean_ctor_get(v___x_2821_, 7);
v_snapshotTasks_2830_ = lean_ctor_get(v___x_2821_, 8);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2858_ == 0)
{
lean_object* v_unused_2859_; 
v_unused_2859_ = lean_ctor_get(v___x_2821_, 5);
lean_dec(v_unused_2859_);
v___x_2832_ = v___x_2821_;
v_isShared_2833_ = v_isSharedCheck_2858_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_snapshotTasks_2830_);
lean_inc(v_infoState_2829_);
lean_inc(v_messages_2828_);
lean_inc(v_traceState_2827_);
lean_inc(v_auxDeclNGen_2826_);
lean_inc(v_ngen_2825_);
lean_inc(v_nextMacroScope_2824_);
lean_inc(v_env_2823_);
lean_dec(v___x_2821_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2858_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v_asyncMode_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2838_; 
v_asyncMode_2834_ = lean_ctor_get(v_toEnvExtension_2822_, 2);
lean_inc(v_asyncMode_2834_);
lean_dec_ref(v_toEnvExtension_2822_);
v___x_2835_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_2815_, v_env_2823_, v_entry_2814_, v_asyncMode_2834_, v___x_2817_);
lean_dec(v_asyncMode_2834_);
v___x_2836_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_2833_ == 0)
{
lean_ctor_set(v___x_2832_, 5, v___x_2836_);
lean_ctor_set(v___x_2832_, 0, v___x_2835_);
v___x_2838_ = v___x_2832_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v___x_2835_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_nextMacroScope_2824_);
lean_ctor_set(v_reuseFailAlloc_2857_, 2, v_ngen_2825_);
lean_ctor_set(v_reuseFailAlloc_2857_, 3, v_auxDeclNGen_2826_);
lean_ctor_set(v_reuseFailAlloc_2857_, 4, v_traceState_2827_);
lean_ctor_set(v_reuseFailAlloc_2857_, 5, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2857_, 6, v_messages_2828_);
lean_ctor_set(v_reuseFailAlloc_2857_, 7, v_infoState_2829_);
lean_ctor_set(v_reuseFailAlloc_2857_, 8, v_snapshotTasks_2830_);
v___x_2838_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v_mctx_2841_; lean_object* v_zetaDeltaFVarIds_2842_; lean_object* v_postponed_2843_; lean_object* v_diag_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2855_; 
v___x_2839_ = lean_st_ref_set(v___y_2820_, v___x_2838_);
v___x_2840_ = lean_st_ref_take(v___y_2819_);
v_mctx_2841_ = lean_ctor_get(v___x_2840_, 0);
v_zetaDeltaFVarIds_2842_ = lean_ctor_get(v___x_2840_, 2);
v_postponed_2843_ = lean_ctor_get(v___x_2840_, 3);
v_diag_2844_ = lean_ctor_get(v___x_2840_, 4);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v___x_2840_, 1);
lean_dec(v_unused_2856_);
v___x_2846_ = v___x_2840_;
v_isShared_2847_ = v_isSharedCheck_2855_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_diag_2844_);
lean_inc(v_postponed_2843_);
lean_inc(v_zetaDeltaFVarIds_2842_);
lean_inc(v_mctx_2841_);
lean_dec(v___x_2840_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2855_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2848_; lean_object* v___x_2850_; 
v___x_2848_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 1, v___x_2848_);
v___x_2850_ = v___x_2846_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_mctx_2841_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v___x_2848_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_zetaDeltaFVarIds_2842_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_postponed_2843_);
lean_ctor_set(v_reuseFailAlloc_2854_, 4, v_diag_2844_);
v___x_2850_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2851_ = lean_st_ref_set(v___y_2819_, v___x_2850_);
v___x_2852_ = lean_box(0);
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___boxed(lean_object* v_mod_2898_, lean_object* v_isMeta_2899_, lean_object* v_hint_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_){
_start:
{
uint8_t v_isMeta_boxed_2906_; lean_object* v_res_2907_; 
v_isMeta_boxed_2906_ = lean_unbox(v_isMeta_2899_);
v_res_2907_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_mod_2898_, v_isMeta_boxed_2906_, v_hint_2900_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v___y_2902_);
lean_dec_ref(v___y_2901_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__9___redArg(lean_object* v_a_2908_, lean_object* v_x_2909_){
_start:
{
if (lean_obj_tag(v_x_2909_) == 0)
{
lean_object* v___x_2910_; 
v___x_2910_ = lean_box(0);
return v___x_2910_;
}
else
{
lean_object* v_key_2911_; lean_object* v_value_2912_; lean_object* v_tail_2913_; uint8_t v___x_2914_; 
v_key_2911_ = lean_ctor_get(v_x_2909_, 0);
v_value_2912_ = lean_ctor_get(v_x_2909_, 1);
v_tail_2913_ = lean_ctor_get(v_x_2909_, 2);
v___x_2914_ = lean_name_eq(v_key_2911_, v_a_2908_);
if (v___x_2914_ == 0)
{
v_x_2909_ = v_tail_2913_;
goto _start;
}
else
{
lean_object* v___x_2916_; 
lean_inc(v_value_2912_);
v___x_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2916_, 0, v_value_2912_);
return v___x_2916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__9___redArg___boxed(lean_object* v_a_2917_, lean_object* v_x_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__9___redArg(v_a_2917_, v_x_2918_);
lean_dec(v_x_2918_);
lean_dec(v_a_2917_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(lean_object* v_m_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v_buckets_2922_; lean_object* v___x_2923_; uint64_t v___y_2925_; 
v_buckets_2922_ = lean_ctor_get(v_m_2920_, 1);
v___x_2923_ = lean_array_get_size(v_buckets_2922_);
if (lean_obj_tag(v_a_2921_) == 0)
{
uint64_t v___x_2939_; 
v___x_2939_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_2925_ = v___x_2939_;
goto v___jp_2924_;
}
else
{
uint64_t v_hash_2940_; 
v_hash_2940_ = lean_ctor_get_uint64(v_a_2921_, sizeof(void*)*2);
v___y_2925_ = v_hash_2940_;
goto v___jp_2924_;
}
v___jp_2924_:
{
uint64_t v___x_2926_; uint64_t v___x_2927_; uint64_t v_fold_2928_; uint64_t v___x_2929_; uint64_t v___x_2930_; uint64_t v___x_2931_; size_t v___x_2932_; size_t v___x_2933_; size_t v___x_2934_; size_t v___x_2935_; size_t v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2926_ = 32ULL;
v___x_2927_ = lean_uint64_shift_right(v___y_2925_, v___x_2926_);
v_fold_2928_ = lean_uint64_xor(v___y_2925_, v___x_2927_);
v___x_2929_ = 16ULL;
v___x_2930_ = lean_uint64_shift_right(v_fold_2928_, v___x_2929_);
v___x_2931_ = lean_uint64_xor(v_fold_2928_, v___x_2930_);
v___x_2932_ = lean_uint64_to_usize(v___x_2931_);
v___x_2933_ = lean_usize_of_nat(v___x_2923_);
v___x_2934_ = ((size_t)1ULL);
v___x_2935_ = lean_usize_sub(v___x_2933_, v___x_2934_);
v___x_2936_ = lean_usize_land(v___x_2932_, v___x_2935_);
v___x_2937_ = lean_array_uget_borrowed(v_buckets_2922_, v___x_2936_);
v___x_2938_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__9___redArg(v_a_2921_, v___x_2937_);
return v___x_2938_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg___boxed(lean_object* v_m_2941_, lean_object* v_a_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_2941_, v_a_2942_);
lean_dec(v_a_2942_);
lean_dec_ref(v_m_2941_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(lean_object* v___x_2944_, lean_object* v_declName_2945_, lean_object* v_as_2946_, size_t v_sz_2947_, size_t v_i_2948_, lean_object* v_b_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_){
_start:
{
uint8_t v___x_2955_; 
v___x_2955_ = lean_usize_dec_lt(v_i_2948_, v_sz_2947_);
if (v___x_2955_ == 0)
{
lean_object* v___x_2956_; 
lean_dec(v_declName_2945_);
v___x_2956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2956_, 0, v_b_2949_);
return v___x_2956_;
}
else
{
lean_object* v___x_2957_; lean_object* v_modules_2958_; lean_object* v___x_2959_; lean_object* v_a_2960_; lean_object* v___x_2961_; lean_object* v_toImport_2962_; lean_object* v_module_2963_; uint8_t v___x_2964_; lean_object* v___x_2965_; 
v___x_2957_ = l_Lean_Environment_header(v___x_2944_);
v_modules_2958_ = lean_ctor_get(v___x_2957_, 3);
lean_inc_ref(v_modules_2958_);
lean_dec_ref(v___x_2957_);
v___x_2959_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_2960_ = lean_array_uget_borrowed(v_as_2946_, v_i_2948_);
v___x_2961_ = lean_array_get(v___x_2959_, v_modules_2958_, v_a_2960_);
lean_dec_ref(v_modules_2958_);
v_toImport_2962_ = lean_ctor_get(v___x_2961_, 0);
lean_inc_ref(v_toImport_2962_);
lean_dec(v___x_2961_);
v_module_2963_ = lean_ctor_get(v_toImport_2962_, 0);
lean_inc(v_module_2963_);
lean_dec_ref(v_toImport_2962_);
v___x_2964_ = 0;
lean_inc(v_declName_2945_);
v___x_2965_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_2963_, v___x_2964_, v_declName_2945_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v___x_2966_; size_t v___x_2967_; size_t v___x_2968_; 
lean_dec_ref(v___x_2965_);
v___x_2966_ = lean_box(0);
v___x_2967_ = ((size_t)1ULL);
v___x_2968_ = lean_usize_add(v_i_2948_, v___x_2967_);
v_i_2948_ = v___x_2968_;
v_b_2949_ = v___x_2966_;
goto _start;
}
else
{
lean_dec(v_declName_2945_);
return v___x_2965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4___boxed(lean_object* v___x_2970_, lean_object* v_declName_2971_, lean_object* v_as_2972_, lean_object* v_sz_2973_, lean_object* v_i_2974_, lean_object* v_b_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_){
_start:
{
size_t v_sz_boxed_2981_; size_t v_i_boxed_2982_; lean_object* v_res_2983_; 
v_sz_boxed_2981_ = lean_unbox_usize(v_sz_2973_);
lean_dec(v_sz_2973_);
v_i_boxed_2982_ = lean_unbox_usize(v_i_2974_);
lean_dec(v_i_2974_);
v_res_2983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v___x_2970_, v_declName_2971_, v_as_2972_, v_sz_boxed_2981_, v_i_boxed_2982_, v_b_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
lean_dec(v___y_2979_);
lean_dec_ref(v___y_2978_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec_ref(v_as_2972_);
lean_dec_ref(v___x_2970_);
return v_res_2983_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2986_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__1));
v___x_2987_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__0));
v___x_2988_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_2987_, v___x_2986_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(lean_object* v_declName_2991_, uint8_t v_isMeta_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
lean_object* v___x_2998_; lean_object* v_env_3002_; lean_object* v___y_3004_; lean_object* v___x_3017_; 
v___x_2998_ = lean_st_ref_get(v___y_2996_);
v_env_3002_ = lean_ctor_get(v___x_2998_, 0);
lean_inc_ref(v_env_3002_);
lean_dec(v___x_2998_);
v___x_3017_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3002_, v_declName_2991_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_dec_ref(v_env_3002_);
lean_dec(v_declName_2991_);
goto v___jp_2999_;
}
else
{
lean_object* v_val_3018_; lean_object* v___x_3019_; lean_object* v_modules_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; 
v_val_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_val_3018_);
lean_dec_ref(v___x_3017_);
v___x_3019_ = l_Lean_Environment_header(v_env_3002_);
v_modules_3020_ = lean_ctor_get(v___x_3019_, 3);
lean_inc_ref(v_modules_3020_);
lean_dec_ref(v___x_3019_);
v___x_3021_ = lean_array_get_size(v_modules_3020_);
v___x_3022_ = lean_nat_dec_lt(v_val_3018_, v___x_3021_);
if (v___x_3022_ == 0)
{
lean_dec_ref(v_modules_3020_);
lean_dec(v_val_3018_);
lean_dec_ref(v_env_3002_);
lean_dec(v_declName_2991_);
goto v___jp_2999_;
}
else
{
lean_object* v___x_3023_; lean_object* v_env_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; uint8_t v___y_3028_; 
v___x_3023_ = lean_st_ref_get(v___y_2996_);
v_env_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc_ref(v_env_3024_);
lean_dec(v___x_3023_);
v___x_3025_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3026_ = lean_array_fget(v_modules_3020_, v_val_3018_);
lean_dec(v_val_3018_);
lean_dec_ref(v_modules_3020_);
if (v_isMeta_2992_ == 0)
{
lean_dec_ref(v_env_3024_);
v___y_3028_ = v_isMeta_2992_;
goto v___jp_3027_;
}
else
{
uint8_t v___x_3039_; 
lean_inc(v_declName_2991_);
v___x_3039_ = l_Lean_isMarkedMeta(v_env_3024_, v_declName_2991_);
if (v___x_3039_ == 0)
{
v___y_3028_ = v_isMeta_2992_;
goto v___jp_3027_;
}
else
{
uint8_t v___x_3040_; 
v___x_3040_ = 0;
v___y_3028_ = v___x_3040_;
goto v___jp_3027_;
}
}
v___jp_3027_:
{
lean_object* v_toImport_3029_; lean_object* v_module_3030_; lean_object* v___x_3031_; 
v_toImport_3029_ = lean_ctor_get(v___x_3026_, 0);
lean_inc_ref(v_toImport_3029_);
lean_dec(v___x_3026_);
v_module_3030_ = lean_ctor_get(v_toImport_3029_, 0);
lean_inc(v_module_3030_);
lean_dec_ref(v_toImport_3029_);
lean_inc(v_declName_2991_);
v___x_3031_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3(v_module_3030_, v___y_3028_, v_declName_2991_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
lean_dec_ref(v___x_3031_);
v___x_3032_ = l_Lean_indirectModUseExt;
v___x_3033_ = lean_box(1);
v___x_3034_ = lean_box(0);
lean_inc_ref(v_env_3002_);
v___x_3035_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3025_, v___x_3032_, v_env_3002_, v___x_3033_, v___x_3034_);
v___x_3036_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3035_, v_declName_2991_);
lean_dec(v___x_3035_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v___x_3037_; 
v___x_3037_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_3004_ = v___x_3037_;
goto v___jp_3003_;
}
else
{
lean_object* v_val_3038_; 
v_val_3038_ = lean_ctor_get(v___x_3036_, 0);
lean_inc(v_val_3038_);
lean_dec_ref(v___x_3036_);
v___y_3004_ = v_val_3038_;
goto v___jp_3003_;
}
}
else
{
lean_dec_ref(v_env_3002_);
lean_dec(v_declName_2991_);
return v___x_3031_;
}
}
}
}
v___jp_2999_:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = lean_box(0);
v___x_3001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3001_, 0, v___x_3000_);
return v___x_3001_;
}
v___jp_3003_:
{
lean_object* v___x_3005_; size_t v_sz_3006_; size_t v___x_3007_; lean_object* v___x_3008_; 
v___x_3005_ = lean_box(0);
v_sz_3006_ = lean_array_size(v___y_3004_);
v___x_3007_ = ((size_t)0ULL);
v___x_3008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__4(v_env_3002_, v_declName_2991_, v___y_3004_, v_sz_3006_, v___x_3007_, v___x_3005_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
lean_dec_ref(v___y_3004_);
lean_dec_ref(v_env_3002_);
if (lean_obj_tag(v___x_3008_) == 0)
{
lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3015_ == 0)
{
lean_object* v_unused_3016_; 
v_unused_3016_ = lean_ctor_get(v___x_3008_, 0);
lean_dec(v_unused_3016_);
v___x_3010_ = v___x_3008_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_dec(v___x_3008_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
lean_ctor_set(v___x_3010_, 0, v___x_3005_);
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3005_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
else
{
return v___x_3008_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___boxed(lean_object* v_declName_3041_, lean_object* v_isMeta_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_){
_start:
{
uint8_t v_isMeta_boxed_3048_; lean_object* v_res_3049_; 
v_isMeta_boxed_3048_ = lean_unbox(v_isMeta_3042_);
v_res_3049_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3041_, v_isMeta_boxed_3048_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
lean_dec(v___y_3044_);
lean_dec_ref(v___y_3043_);
return v_res_3049_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(lean_object* v___y_3050_, uint8_t v_isExporting_3051_, lean_object* v___x_3052_, lean_object* v___y_3053_, lean_object* v___x_3054_, lean_object* v_a_x3f_3055_){
_start:
{
lean_object* v___x_3057_; lean_object* v_env_3058_; lean_object* v_nextMacroScope_3059_; lean_object* v_ngen_3060_; lean_object* v_auxDeclNGen_3061_; lean_object* v_traceState_3062_; lean_object* v_messages_3063_; lean_object* v_infoState_3064_; lean_object* v_snapshotTasks_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3090_; 
v___x_3057_ = lean_st_ref_take(v___y_3050_);
v_env_3058_ = lean_ctor_get(v___x_3057_, 0);
v_nextMacroScope_3059_ = lean_ctor_get(v___x_3057_, 1);
v_ngen_3060_ = lean_ctor_get(v___x_3057_, 2);
v_auxDeclNGen_3061_ = lean_ctor_get(v___x_3057_, 3);
v_traceState_3062_ = lean_ctor_get(v___x_3057_, 4);
v_messages_3063_ = lean_ctor_get(v___x_3057_, 6);
v_infoState_3064_ = lean_ctor_get(v___x_3057_, 7);
v_snapshotTasks_3065_ = lean_ctor_get(v___x_3057_, 8);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3090_ == 0)
{
lean_object* v_unused_3091_; 
v_unused_3091_ = lean_ctor_get(v___x_3057_, 5);
lean_dec(v_unused_3091_);
v___x_3067_ = v___x_3057_;
v_isShared_3068_ = v_isSharedCheck_3090_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_snapshotTasks_3065_);
lean_inc(v_infoState_3064_);
lean_inc(v_messages_3063_);
lean_inc(v_traceState_3062_);
lean_inc(v_auxDeclNGen_3061_);
lean_inc(v_ngen_3060_);
lean_inc(v_nextMacroScope_3059_);
lean_inc(v_env_3058_);
lean_dec(v___x_3057_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3090_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3069_; lean_object* v___x_3071_; 
v___x_3069_ = l_Lean_Environment_setExporting(v_env_3058_, v_isExporting_3051_);
if (v_isShared_3068_ == 0)
{
lean_ctor_set(v___x_3067_, 5, v___x_3052_);
lean_ctor_set(v___x_3067_, 0, v___x_3069_);
v___x_3071_ = v___x_3067_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v___x_3069_);
lean_ctor_set(v_reuseFailAlloc_3089_, 1, v_nextMacroScope_3059_);
lean_ctor_set(v_reuseFailAlloc_3089_, 2, v_ngen_3060_);
lean_ctor_set(v_reuseFailAlloc_3089_, 3, v_auxDeclNGen_3061_);
lean_ctor_set(v_reuseFailAlloc_3089_, 4, v_traceState_3062_);
lean_ctor_set(v_reuseFailAlloc_3089_, 5, v___x_3052_);
lean_ctor_set(v_reuseFailAlloc_3089_, 6, v_messages_3063_);
lean_ctor_set(v_reuseFailAlloc_3089_, 7, v_infoState_3064_);
lean_ctor_set(v_reuseFailAlloc_3089_, 8, v_snapshotTasks_3065_);
v___x_3071_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v_mctx_3074_; lean_object* v_zetaDeltaFVarIds_3075_; lean_object* v_postponed_3076_; lean_object* v_diag_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3087_; 
v___x_3072_ = lean_st_ref_set(v___y_3050_, v___x_3071_);
v___x_3073_ = lean_st_ref_take(v___y_3053_);
v_mctx_3074_ = lean_ctor_get(v___x_3073_, 0);
v_zetaDeltaFVarIds_3075_ = lean_ctor_get(v___x_3073_, 2);
v_postponed_3076_ = lean_ctor_get(v___x_3073_, 3);
v_diag_3077_ = lean_ctor_get(v___x_3073_, 4);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3087_ == 0)
{
lean_object* v_unused_3088_; 
v_unused_3088_ = lean_ctor_get(v___x_3073_, 1);
lean_dec(v_unused_3088_);
v___x_3079_ = v___x_3073_;
v_isShared_3080_ = v_isSharedCheck_3087_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_diag_3077_);
lean_inc(v_postponed_3076_);
lean_inc(v_zetaDeltaFVarIds_3075_);
lean_inc(v_mctx_3074_);
lean_dec(v___x_3073_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3087_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
lean_ctor_set(v___x_3079_, 1, v___x_3054_);
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_mctx_3074_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___x_3054_);
lean_ctor_set(v_reuseFailAlloc_3086_, 2, v_zetaDeltaFVarIds_3075_);
lean_ctor_set(v_reuseFailAlloc_3086_, 3, v_postponed_3076_);
lean_ctor_set(v_reuseFailAlloc_3086_, 4, v_diag_3077_);
v___x_3082_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3083_ = lean_st_ref_set(v___y_3053_, v___x_3082_);
v___x_3084_ = lean_box(0);
v___x_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
return v___x_3085_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0___boxed(lean_object* v___y_3092_, lean_object* v_isExporting_3093_, lean_object* v___x_3094_, lean_object* v___y_3095_, lean_object* v___x_3096_, lean_object* v_a_x3f_3097_, lean_object* v___y_3098_){
_start:
{
uint8_t v_isExporting_boxed_3099_; lean_object* v_res_3100_; 
v_isExporting_boxed_3099_ = lean_unbox(v_isExporting_3093_);
v_res_3100_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3092_, v_isExporting_boxed_3099_, v___x_3094_, v___y_3095_, v___x_3096_, v_a_x3f_3097_);
lean_dec(v_a_x3f_3097_);
lean_dec(v___y_3095_);
lean_dec(v___y_3092_);
return v_res_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(lean_object* v_x_3101_, uint8_t v_isExporting_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v___x_3108_; lean_object* v_env_3109_; uint8_t v_isExporting_3110_; lean_object* v___x_3111_; lean_object* v_env_3112_; lean_object* v_nextMacroScope_3113_; lean_object* v_ngen_3114_; lean_object* v_auxDeclNGen_3115_; lean_object* v_traceState_3116_; lean_object* v_messages_3117_; lean_object* v_infoState_3118_; lean_object* v_snapshotTasks_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3173_; 
v___x_3108_ = lean_st_ref_get(v___y_3106_);
v_env_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc_ref(v_env_3109_);
lean_dec(v___x_3108_);
v_isExporting_3110_ = lean_ctor_get_uint8(v_env_3109_, sizeof(void*)*8);
lean_dec_ref(v_env_3109_);
v___x_3111_ = lean_st_ref_take(v___y_3106_);
v_env_3112_ = lean_ctor_get(v___x_3111_, 0);
v_nextMacroScope_3113_ = lean_ctor_get(v___x_3111_, 1);
v_ngen_3114_ = lean_ctor_get(v___x_3111_, 2);
v_auxDeclNGen_3115_ = lean_ctor_get(v___x_3111_, 3);
v_traceState_3116_ = lean_ctor_get(v___x_3111_, 4);
v_messages_3117_ = lean_ctor_get(v___x_3111_, 6);
v_infoState_3118_ = lean_ctor_get(v___x_3111_, 7);
v_snapshotTasks_3119_ = lean_ctor_get(v___x_3111_, 8);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3173_ == 0)
{
lean_object* v_unused_3174_; 
v_unused_3174_ = lean_ctor_get(v___x_3111_, 5);
lean_dec(v_unused_3174_);
v___x_3121_ = v___x_3111_;
v_isShared_3122_ = v_isSharedCheck_3173_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_snapshotTasks_3119_);
lean_inc(v_infoState_3118_);
lean_inc(v_messages_3117_);
lean_inc(v_traceState_3116_);
lean_inc(v_auxDeclNGen_3115_);
lean_inc(v_ngen_3114_);
lean_inc(v_nextMacroScope_3113_);
lean_inc(v_env_3112_);
lean_dec(v___x_3111_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3173_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3123_ = l_Lean_Environment_setExporting(v_env_3112_, v_isExporting_3102_);
v___x_3124_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 5, v___x_3124_);
lean_ctor_set(v___x_3121_, 0, v___x_3123_);
v___x_3126_ = v___x_3121_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3123_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v_nextMacroScope_3113_);
lean_ctor_set(v_reuseFailAlloc_3172_, 2, v_ngen_3114_);
lean_ctor_set(v_reuseFailAlloc_3172_, 3, v_auxDeclNGen_3115_);
lean_ctor_set(v_reuseFailAlloc_3172_, 4, v_traceState_3116_);
lean_ctor_set(v_reuseFailAlloc_3172_, 5, v___x_3124_);
lean_ctor_set(v_reuseFailAlloc_3172_, 6, v_messages_3117_);
lean_ctor_set(v_reuseFailAlloc_3172_, 7, v_infoState_3118_);
lean_ctor_set(v_reuseFailAlloc_3172_, 8, v_snapshotTasks_3119_);
v___x_3126_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v_mctx_3129_; lean_object* v_zetaDeltaFVarIds_3130_; lean_object* v_postponed_3131_; lean_object* v_diag_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3170_; 
v___x_3127_ = lean_st_ref_set(v___y_3106_, v___x_3126_);
v___x_3128_ = lean_st_ref_take(v___y_3104_);
v_mctx_3129_ = lean_ctor_get(v___x_3128_, 0);
v_zetaDeltaFVarIds_3130_ = lean_ctor_get(v___x_3128_, 2);
v_postponed_3131_ = lean_ctor_get(v___x_3128_, 3);
v_diag_3132_ = lean_ctor_get(v___x_3128_, 4);
v_isSharedCheck_3170_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; 
v_unused_3171_ = lean_ctor_get(v___x_3128_, 1);
lean_dec(v_unused_3171_);
v___x_3134_ = v___x_3128_;
v_isShared_3135_ = v_isSharedCheck_3170_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_diag_3132_);
lean_inc(v_postponed_3131_);
lean_inc(v_zetaDeltaFVarIds_3130_);
lean_inc(v_mctx_3129_);
lean_dec(v___x_3128_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3170_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3138_; 
v___x_3136_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_eraseEMatchAttr___closed__0);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 1, v___x_3136_);
v___x_3138_ = v___x_3134_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_mctx_3129_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v___x_3136_);
lean_ctor_set(v_reuseFailAlloc_3169_, 2, v_zetaDeltaFVarIds_3130_);
lean_ctor_set(v_reuseFailAlloc_3169_, 3, v_postponed_3131_);
lean_ctor_set(v_reuseFailAlloc_3169_, 4, v_diag_3132_);
v___x_3138_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
lean_object* v___x_3139_; lean_object* v_r_3140_; 
v___x_3139_ = lean_st_ref_set(v___y_3104_, v___x_3138_);
lean_inc(v___y_3106_);
lean_inc(v___y_3104_);
v_r_3140_ = lean_apply_5(v_x_3101_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_, lean_box(0));
if (lean_obj_tag(v_r_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3157_; 
v_a_3141_ = lean_ctor_get(v_r_3140_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v_r_3140_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3143_ = v_r_3140_;
v_isShared_3144_ = v_isSharedCheck_3157_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v_r_3140_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3157_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
lean_inc(v_a_3141_);
if (v_isShared_3144_ == 0)
{
lean_ctor_set_tag(v___x_3143_, 1);
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
lean_object* v___x_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
v___x_3147_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3106_, v_isExporting_3110_, v___x_3124_, v___y_3104_, v___x_3136_, v___x_3146_);
lean_dec_ref(v___x_3146_);
lean_dec(v___y_3104_);
lean_dec(v___y_3106_);
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
lean_ctor_set(v___x_3149_, 0, v_a_3141_);
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3141_);
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
else
{
lean_object* v_a_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
v_a_3158_ = lean_ctor_get(v_r_3140_, 0);
lean_inc(v_a_3158_);
lean_dec_ref(v_r_3140_);
v___x_3159_ = lean_box(0);
v___x_3160_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___lam__0(v___y_3106_, v_isExporting_3110_, v___x_3124_, v___y_3104_, v___x_3136_, v___x_3159_);
lean_dec(v___y_3104_);
lean_dec(v___y_3106_);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3167_ == 0)
{
lean_object* v_unused_3168_; 
v_unused_3168_ = lean_ctor_get(v___x_3160_, 0);
lean_dec(v_unused_3168_);
v___x_3162_ = v___x_3160_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_dec(v___x_3160_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set_tag(v___x_3162_, 1);
lean_ctor_set(v___x_3162_, 0, v_a_3158_);
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3158_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg___boxed(lean_object* v_x_3175_, lean_object* v_isExporting_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
uint8_t v_isExporting_boxed_3182_; lean_object* v_res_3183_; 
v_isExporting_boxed_3182_ = lean_unbox(v_isExporting_3176_);
v_res_3183_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3175_, v_isExporting_boxed_3182_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_);
return v_res_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(lean_object* v_x_3184_, uint8_t v_when_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
if (v_when_3185_ == 0)
{
lean_object* v___x_3191_; 
v___x_3191_ = lean_apply_5(v_x_3184_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, lean_box(0));
return v___x_3191_;
}
else
{
uint8_t v___x_3192_; lean_object* v___x_3193_; 
v___x_3192_ = 0;
v___x_3193_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3184_, v___x_3192_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
return v___x_3193_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg___boxed(lean_object* v_x_3194_, lean_object* v_when_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_){
_start:
{
uint8_t v_when_boxed_3201_; lean_object* v_res_3202_; 
v_when_boxed_3201_ = lean_unbox(v_when_3195_);
v_res_3202_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3194_, v_when_boxed_3201_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(lean_object* v___x_3203_, lean_object* v_ext_3204_, uint8_t v_showInfo_3205_, uint8_t v_minIndexable_3206_, lean_object* v_attrName_3207_, lean_object* v_declName_3208_, lean_object* v_stx_3209_, uint8_t v_attrKind_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
uint8_t v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; uint8_t v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___y_3231_; lean_object* v___x_3241_; 
v___x_3214_ = 0;
v___x_3215_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_3216_ = lean_unsigned_to_nat(32u);
v___x_3217_ = lean_mk_empty_array_with_capacity(v___x_3216_);
lean_dec_ref(v___x_3217_);
v___x_3218_ = lean_unsigned_to_nat(0u);
v___x_3219_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0___closed__4);
v___x_3220_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__2);
v___x_3221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__3));
v___x_3222_ = lean_box(0);
v___x_3223_ = 1;
lean_inc(v___x_3203_);
v___x_3224_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3224_, 0, v___x_3215_);
lean_ctor_set(v___x_3224_, 1, v___x_3203_);
lean_ctor_set(v___x_3224_, 2, v___x_3220_);
lean_ctor_set(v___x_3224_, 3, v___x_3221_);
lean_ctor_set(v___x_3224_, 4, v___x_3222_);
lean_ctor_set(v___x_3224_, 5, v___x_3218_);
lean_ctor_set(v___x_3224_, 6, v___x_3222_);
lean_ctor_set_uint8(v___x_3224_, sizeof(void*)*7, v___x_3214_);
lean_ctor_set_uint8(v___x_3224_, sizeof(void*)*7 + 1, v___x_3214_);
lean_ctor_set_uint8(v___x_3224_, sizeof(void*)*7 + 2, v___x_3214_);
lean_ctor_set_uint8(v___x_3224_, sizeof(void*)*7 + 3, v___x_3223_);
v___x_3225_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__4);
v___x_3226_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__5);
v___x_3227_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___closed__6);
v___x_3228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3225_);
lean_ctor_set(v___x_3228_, 1, v___x_3226_);
lean_ctor_set(v___x_3228_, 2, v___x_3203_);
lean_ctor_set(v___x_3228_, 3, v___x_3219_);
lean_ctor_set(v___x_3228_, 4, v___x_3227_);
v___x_3229_ = lean_st_mk_ref(v___x_3228_);
lean_inc(v_declName_3208_);
v___x_3241_ = l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2(v_declName_3208_, v___x_3214_, v___x_3224_, v___x_3229_, v___y_3211_, v___y_3212_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___f_3246_; lean_object* v___x_3247_; 
lean_dec_ref(v___x_3241_);
v___x_3242_ = lean_box(v_attrKind_3210_);
v___x_3243_ = lean_box(v_showInfo_3205_);
v___x_3244_ = lean_box(v_minIndexable_3206_);
v___x_3245_ = lean_box(v___x_3214_);
v___f_3246_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___boxed), 13, 8);
lean_closure_set(v___f_3246_, 0, v_stx_3209_);
lean_closure_set(v___f_3246_, 1, v_ext_3204_);
lean_closure_set(v___f_3246_, 2, v_declName_3208_);
lean_closure_set(v___f_3246_, 3, v___x_3242_);
lean_closure_set(v___f_3246_, 4, v___x_3243_);
lean_closure_set(v___f_3246_, 5, v___x_3244_);
lean_closure_set(v___f_3246_, 6, v___x_3245_);
lean_closure_set(v___f_3246_, 7, v_attrName_3207_);
lean_inc(v___x_3229_);
v___x_3247_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v___f_3246_, v___x_3223_, v___x_3224_, v___x_3229_, v___y_3211_, v___y_3212_);
v___y_3231_ = v___x_3247_;
goto v___jp_3230_;
}
else
{
lean_dec_ref(v___x_3224_);
lean_dec(v___y_3212_);
lean_dec_ref(v___y_3211_);
lean_dec(v_stx_3209_);
lean_dec(v_declName_3208_);
lean_dec(v_attrName_3207_);
lean_dec_ref(v_ext_3204_);
v___y_3231_ = v___x_3241_;
goto v___jp_3230_;
}
v___jp_3230_:
{
if (lean_obj_tag(v___y_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3240_; 
v_a_3232_ = lean_ctor_get(v___y_3231_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___y_3231_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3234_ = v___y_3231_;
v_isShared_3235_ = v_isSharedCheck_3240_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___y_3231_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3240_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3236_ = lean_st_ref_get(v___x_3229_);
lean_dec(v___x_3229_);
lean_dec(v___x_3236_);
if (v_isShared_3235_ == 0)
{
v___x_3238_ = v___x_3234_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3232_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
else
{
lean_dec(v___x_3229_);
return v___y_3231_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed(lean_object* v___x_3248_, lean_object* v_ext_3249_, lean_object* v_showInfo_3250_, lean_object* v_minIndexable_3251_, lean_object* v_attrName_3252_, lean_object* v_declName_3253_, lean_object* v_stx_3254_, lean_object* v_attrKind_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
uint8_t v_showInfo_boxed_3259_; uint8_t v_minIndexable_boxed_3260_; uint8_t v_attrKind_boxed_3261_; lean_object* v_res_3262_; 
v_showInfo_boxed_3259_ = lean_unbox(v_showInfo_3250_);
v_minIndexable_boxed_3260_ = lean_unbox(v_minIndexable_3251_);
v_attrKind_boxed_3261_ = lean_unbox(v_attrKind_3255_);
v_res_3262_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3(v___x_3248_, v_ext_3249_, v_showInfo_boxed_3259_, v_minIndexable_boxed_3260_, v_attrName_3252_, v_declName_3253_, v_stx_3254_, v_attrKind_boxed_3261_, v___y_3256_, v___y_3257_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(lean_object* v_attrName_3285_, uint8_t v_minIndexable_3286_, uint8_t v_showInfo_3287_, lean_object* v_ext_3288_, lean_object* v_ref_3289_){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___f_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___f_3296_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3342_; 
v___x_3291_ = lean_box(1);
v___x_3292_ = lean_box(v_showInfo_3287_);
lean_inc(v_attrName_3285_);
lean_inc_ref(v_ext_3288_);
v___f_3293_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__1___boxed), 8, 4);
lean_closure_set(v___f_3293_, 0, v___x_3291_);
lean_closure_set(v___f_3293_, 1, v_ext_3288_);
lean_closure_set(v___f_3293_, 2, v___x_3292_);
lean_closure_set(v___f_3293_, 3, v_attrName_3285_);
v___x_3294_ = lean_box(v_showInfo_3287_);
v___x_3295_ = lean_box(v_minIndexable_3286_);
lean_inc(v_attrName_3285_);
v___f_3296_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__3___boxed), 11, 5);
lean_closure_set(v___f_3296_, 0, v___x_3291_);
lean_closure_set(v___f_3296_, 1, v_ext_3288_);
lean_closure_set(v___f_3296_, 2, v___x_3294_);
lean_closure_set(v___f_3296_, 3, v___x_3295_);
lean_closure_set(v___f_3296_, 4, v_attrName_3285_);
if (v_minIndexable_3286_ == 0)
{
if (v_showInfo_3287_ == 0)
{
lean_inc(v_attrName_3285_);
v___y_3342_ = v_attrName_3285_;
goto v___jp_3341_;
}
else
{
lean_object* v___x_3370_; lean_object* v___x_3371_; 
v___x_3370_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__19));
lean_inc(v_attrName_3285_);
v___x_3371_ = lean_name_append_after(v_attrName_3285_, v___x_3370_);
v___y_3342_ = v___x_3371_;
goto v___jp_3341_;
}
}
else
{
if (v_showInfo_3287_ == 0)
{
lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3372_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__20));
lean_inc(v_attrName_3285_);
v___x_3373_ = lean_name_append_after(v_attrName_3285_, v___x_3372_);
v___y_3342_ = v___x_3373_;
goto v___jp_3341_;
}
else
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3374_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__21));
lean_inc(v_attrName_3285_);
v___x_3375_ = lean_name_append_after(v_attrName_3285_, v___x_3374_);
v___y_3342_ = v___x_3375_;
goto v___jp_3341_;
}
}
v___jp_3297_:
{
lean_object* v___x_3300_; uint8_t v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; uint8_t v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3300_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__0));
v___x_3301_ = 1;
v___x_3302_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3285_, v___x_3301_);
v___x_3303_ = lean_string_append(v___x_3300_, v___x_3302_);
v___x_3304_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__1));
v___x_3305_ = lean_string_append(v___x_3303_, v___x_3304_);
v___x_3306_ = lean_string_append(v___x_3305_, v___x_3302_);
v___x_3307_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__2));
v___x_3308_ = lean_string_append(v___x_3306_, v___x_3307_);
v___x_3309_ = lean_string_append(v___x_3308_, v___x_3302_);
v___x_3310_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__3));
v___x_3311_ = lean_string_append(v___x_3309_, v___x_3310_);
v___x_3312_ = lean_string_append(v___x_3311_, v___x_3302_);
v___x_3313_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__4));
v___x_3314_ = lean_string_append(v___x_3312_, v___x_3313_);
v___x_3315_ = lean_string_append(v___x_3314_, v___x_3302_);
v___x_3316_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__5));
v___x_3317_ = lean_string_append(v___x_3315_, v___x_3316_);
v___x_3318_ = lean_string_append(v___x_3317_, v___x_3302_);
v___x_3319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__6));
v___x_3320_ = lean_string_append(v___x_3318_, v___x_3319_);
v___x_3321_ = lean_string_append(v___x_3320_, v___x_3302_);
v___x_3322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__7));
v___x_3323_ = lean_string_append(v___x_3321_, v___x_3322_);
v___x_3324_ = lean_string_append(v___x_3323_, v___x_3302_);
v___x_3325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__8));
v___x_3326_ = lean_string_append(v___x_3324_, v___x_3325_);
v___x_3327_ = lean_string_append(v___x_3326_, v___x_3302_);
v___x_3328_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__9));
v___x_3329_ = lean_string_append(v___x_3327_, v___x_3328_);
v___x_3330_ = lean_string_append(v___x_3329_, v___x_3302_);
v___x_3331_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__10));
v___x_3332_ = lean_string_append(v___x_3330_, v___x_3331_);
v___x_3333_ = lean_string_append(v___x_3332_, v___x_3302_);
lean_dec_ref(v___x_3302_);
v___x_3334_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__11));
v___x_3335_ = lean_string_append(v___x_3333_, v___x_3334_);
v___x_3336_ = lean_string_append(v___y_3299_, v___x_3335_);
lean_dec_ref(v___x_3335_);
v___x_3337_ = 1;
v___x_3338_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3338_, 0, v_ref_3289_);
lean_ctor_set(v___x_3338_, 1, v___y_3298_);
lean_ctor_set(v___x_3338_, 2, v___x_3336_);
lean_ctor_set_uint8(v___x_3338_, sizeof(void*)*3, v___x_3337_);
v___x_3339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3338_);
lean_ctor_set(v___x_3339_, 1, v___f_3296_);
lean_ctor_set(v___x_3339_, 2, v___f_3293_);
v___x_3340_ = l_Lean_registerBuiltinAttribute(v___x_3339_);
return v___x_3340_;
}
v___jp_3341_:
{
if (v_minIndexable_3286_ == 0)
{
if (v_showInfo_3287_ == 0)
{
lean_object* v___x_3343_; uint8_t v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3343_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
v___x_3344_ = 1;
lean_inc(v_attrName_3285_);
v___x_3345_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3285_, v___x_3344_);
v___x_3346_ = lean_string_append(v___x_3343_, v___x_3345_);
lean_dec_ref(v___x_3345_);
v___x_3347_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__13));
v___x_3348_ = lean_string_append(v___x_3346_, v___x_3347_);
v___y_3298_ = v___y_3342_;
v___y_3299_ = v___x_3348_;
goto v___jp_3297_;
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3285_);
v___x_3350_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3285_, v_showInfo_3287_);
v___x_3351_ = lean_string_append(v___x_3349_, v___x_3350_);
v___x_3352_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__14));
v___x_3353_ = lean_string_append(v___x_3351_, v___x_3352_);
v___x_3354_ = lean_string_append(v___x_3353_, v___x_3350_);
lean_dec_ref(v___x_3350_);
v___x_3355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__15));
v___x_3356_ = lean_string_append(v___x_3354_, v___x_3355_);
v___y_3298_ = v___y_3342_;
v___y_3299_ = v___x_3356_;
goto v___jp_3297_;
}
}
else
{
if (v_showInfo_3287_ == 0)
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3357_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3285_);
v___x_3358_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3285_, v_minIndexable_3286_);
v___x_3359_ = lean_string_append(v___x_3357_, v___x_3358_);
lean_dec_ref(v___x_3358_);
v___x_3360_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__16));
v___x_3361_ = lean_string_append(v___x_3359_, v___x_3360_);
v___y_3298_ = v___y_3342_;
v___y_3299_ = v___x_3361_;
goto v___jp_3297_;
}
else
{
lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__12));
lean_inc(v_attrName_3285_);
v___x_3363_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_attrName_3285_, v_showInfo_3287_);
v___x_3364_ = lean_string_append(v___x_3362_, v___x_3363_);
v___x_3365_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__17));
v___x_3366_ = lean_string_append(v___x_3364_, v___x_3365_);
v___x_3367_ = lean_string_append(v___x_3366_, v___x_3363_);
lean_dec_ref(v___x_3363_);
v___x_3368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___closed__18));
v___x_3369_ = lean_string_append(v___x_3367_, v___x_3368_);
v___y_3298_ = v___y_3342_;
v___y_3299_ = v___x_3369_;
goto v___jp_3297_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___boxed(lean_object* v_attrName_3376_, lean_object* v_minIndexable_3377_, lean_object* v_showInfo_3378_, lean_object* v_ext_3379_, lean_object* v_ref_3380_, lean_object* v_a_3381_){
_start:
{
uint8_t v_minIndexable_boxed_3382_; uint8_t v_showInfo_boxed_3383_; lean_object* v_res_3384_; 
v_minIndexable_boxed_3382_ = lean_unbox(v_minIndexable_3377_);
v_showInfo_boxed_3383_ = lean_unbox(v_showInfo_3378_);
v_res_3384_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3376_, v_minIndexable_boxed_3382_, v_showInfo_boxed_3383_, v_ext_3379_, v_ref_3380_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(lean_object* v_00_u03b1_3385_, lean_object* v_msg_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___redArg(v_msg_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_);
return v___x_3392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0___boxed(lean_object* v_00_u03b1_3393_, lean_object* v_msg_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__0(v_00_u03b1_3393_, v_msg_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
lean_dec_ref(v___y_3395_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(lean_object* v_ext_3401_, uint8_t v_attrKind_3402_, uint8_t v_showInfo_3403_, uint8_t v_minIndexable_3404_, lean_object* v_as_3405_, lean_object* v_as_x27_3406_, lean_object* v_b_3407_, lean_object* v_a_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v___x_3414_; 
v___x_3414_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___redArg(v_ext_3401_, v_attrKind_3402_, v_showInfo_3403_, v_minIndexable_3404_, v_as_x27_3406_, v_b_3407_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1___boxed(lean_object* v_ext_3415_, lean_object* v_attrKind_3416_, lean_object* v_showInfo_3417_, lean_object* v_minIndexable_3418_, lean_object* v_as_3419_, lean_object* v_as_x27_3420_, lean_object* v_b_3421_, lean_object* v_a_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
uint8_t v_attrKind_boxed_3428_; uint8_t v_showInfo_boxed_3429_; uint8_t v_minIndexable_boxed_3430_; lean_object* v_res_3431_; 
v_attrKind_boxed_3428_ = lean_unbox(v_attrKind_3416_);
v_showInfo_boxed_3429_ = lean_unbox(v_showInfo_3417_);
v_minIndexable_boxed_3430_ = lean_unbox(v_minIndexable_3418_);
v_res_3431_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__1(v_ext_3415_, v_attrKind_boxed_3428_, v_showInfo_boxed_3429_, v_minIndexable_boxed_3430_, v_as_3419_, v_as_x27_3420_, v_b_3421_, v_a_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
lean_dec(v_as_3419_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(lean_object* v_00_u03b1_3432_, lean_object* v_x_3433_, uint8_t v_isExporting_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_){
_start:
{
lean_object* v___x_3440_; 
v___x_3440_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___redArg(v_x_3433_, v_isExporting_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
return v___x_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7___boxed(lean_object* v_00_u03b1_3441_, lean_object* v_x_3442_, lean_object* v_isExporting_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_){
_start:
{
uint8_t v_isExporting_boxed_3449_; lean_object* v_res_3450_; 
v_isExporting_boxed_3449_ = lean_unbox(v_isExporting_3443_);
v_res_3450_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3_spec__7(v_00_u03b1_3441_, v_x_3442_, v_isExporting_boxed_3449_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(lean_object* v_00_u03b1_3451_, lean_object* v_x_3452_, uint8_t v_when_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_){
_start:
{
lean_object* v___x_3459_; 
v___x_3459_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___redArg(v_x_3452_, v_when_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_);
return v___x_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3___boxed(lean_object* v_00_u03b1_3460_, lean_object* v_x_3461_, lean_object* v_when_3462_, lean_object* v___y_3463_, lean_object* v___y_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
uint8_t v_when_boxed_3468_; lean_object* v_res_3469_; 
v_when_boxed_3468_ = lean_unbox(v_when_3462_);
v_res_3469_ = l_Lean_withoutExporting___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__3(v_00_u03b1_3460_, v_x_3461_, v_when_boxed_3468_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_);
return v_res_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(lean_object* v_cls_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_){
_start:
{
lean_object* v___x_3476_; 
v___x_3476_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg(v_cls_3470_, v___y_3473_);
return v___x_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___boxed(lean_object* v_cls_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5(v_cls_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(lean_object* v_00_u03b2_3484_, lean_object* v_m_3485_, lean_object* v_a_3486_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v_m_3485_, v_a_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3488_, lean_object* v_m_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v_res_3491_; 
v_res_3491_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5(v_00_u03b2_3488_, v_m_3489_, v_a_3490_);
lean_dec(v_a_3490_);
lean_dec_ref(v_m_3489_);
return v_res_3491_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3492_, lean_object* v_x_3493_, lean_object* v_x_3494_){
_start:
{
uint8_t v___x_3495_; 
v___x_3495_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v_x_3493_, v_x_3494_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3496_, lean_object* v_x_3497_, lean_object* v_x_3498_){
_start:
{
uint8_t v_res_3499_; lean_object* v_r_3500_; 
v_res_3499_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4(v_00_u03b2_3496_, v_x_3497_, v_x_3498_);
lean_dec_ref(v_x_3498_);
v_r_3500_ = lean_box(v_res_3499_);
return v_r_3500_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_3501_, lean_object* v_a_3502_, lean_object* v_x_3503_){
_start:
{
lean_object* v___x_3504_; 
v___x_3504_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__9___redArg(v_a_3502_, v_x_3503_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__9___boxed(lean_object* v_00_u03b2_3505_, lean_object* v_a_3506_, lean_object* v_x_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5_spec__9(v_00_u03b2_3505_, v_a_3506_, v_x_3507_);
lean_dec(v_x_3507_);
lean_dec(v_a_3506_);
return v_res_3508_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(lean_object* v_00_u03b2_3509_, lean_object* v_x_3510_, size_t v_x_3511_, lean_object* v_x_3512_){
_start:
{
uint8_t v___x_3513_; 
v___x_3513_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___redArg(v_x_3510_, v_x_3511_, v_x_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7___boxed(lean_object* v_00_u03b2_3514_, lean_object* v_x_3515_, lean_object* v_x_3516_, lean_object* v_x_3517_){
_start:
{
size_t v_x_17485__boxed_3518_; uint8_t v_res_3519_; lean_object* v_r_3520_; 
v_x_17485__boxed_3518_ = lean_unbox_usize(v_x_3516_);
lean_dec(v_x_3516_);
v_res_3519_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7(v_00_u03b2_3514_, v_x_3515_, v_x_17485__boxed_3518_, v_x_3517_);
lean_dec_ref(v_x_3517_);
v_r_3520_ = lean_box(v_res_3519_);
return v_r_3520_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__11(lean_object* v_00_u03b2_3521_, lean_object* v_keys_3522_, lean_object* v_vals_3523_, lean_object* v_heq_3524_, lean_object* v_i_3525_, lean_object* v_k_3526_){
_start:
{
uint8_t v___x_3527_; 
v___x_3527_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__11___redArg(v_keys_3522_, v_i_3525_, v_k_3526_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__11___boxed(lean_object* v_00_u03b2_3528_, lean_object* v_keys_3529_, lean_object* v_vals_3530_, lean_object* v_heq_3531_, lean_object* v_i_3532_, lean_object* v_k_3533_){
_start:
{
uint8_t v_res_3534_; lean_object* v_r_3535_; 
v_res_3534_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4_spec__7_spec__11(v_00_u03b2_3528_, v_keys_3529_, v_vals_3530_, v_heq_3531_, v_i_3532_, v_k_3533_);
lean_dec_ref(v_k_3533_);
lean_dec_ref(v_vals_3530_);
lean_dec_ref(v_keys_3529_);
v_r_3535_ = lean_box(v_res_3534_);
return v_r_3535_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3536_ = lean_box(0);
v___x_3537_ = lean_unsigned_to_nat(16u);
v___x_3538_ = lean_mk_array(v___x_3537_, v___x_3536_);
return v___x_3538_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = lean_obj_once(&l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3540_ = lean_unsigned_to_nat(0u);
v___x_3541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3541_, 0, v___x_3540_);
lean_ctor_set(v___x_3541_, 1, v___x_3539_);
return v___x_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3543_ = lean_obj_once(&l_Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_, &l_Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2__once, _init_l_Lean_Meta_Grind_initFn___closed__1_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_);
v___x_3544_ = lean_st_mk_ref(v___x_3543_);
v___x_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
return v___x_3545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2____boxed(lean_object* v_a_3546_){
_start:
{
lean_object* v_res_3547_; 
v_res_3547_ = l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_cls_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_options_3551_; uint8_t v_hasTrace_3552_; 
v_options_3551_ = lean_ctor_get(v___y_3549_, 2);
v_hasTrace_3552_ = lean_ctor_get_uint8(v_options_3551_, sizeof(void*)*1);
if (v_hasTrace_3552_ == 0)
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
lean_dec(v_cls_3548_);
v___x_3553_ = lean_box(v_hasTrace_3552_);
v___x_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
return v___x_3554_;
}
else
{
lean_object* v_inheritedTraceOptions_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v_inheritedTraceOptions_3555_ = lean_ctor_get(v___y_3549_, 13);
v___x_3556_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__5___redArg___closed__1));
v___x_3557_ = l_Lean_Name_append(v___x_3556_, v_cls_3548_);
v___x_3558_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3555_, v_options_3551_, v___x_3557_);
lean_dec(v___x_3557_);
v___x_3559_ = lean_box(v___x_3558_);
v___x_3560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
return v___x_3560_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_cls_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___redArg(v_cls_3561_, v___y_3562_);
lean_dec_ref(v___y_3562_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__2(lean_object* v_cls_3565_, lean_object* v_msg_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
lean_object* v_ref_3570_; lean_object* v___x_3571_; lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3616_; 
v_ref_3570_ = lean_ctor_get(v___y_3567_, 5);
v___x_3571_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Grind_getAttrKindCore_spec__0_spec__0(v_msg_3566_, v___y_3567_, v___y_3568_);
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3574_ = v___x_3571_;
v_isShared_3575_ = v_isSharedCheck_3616_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3571_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3616_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v_traceState_3577_; lean_object* v_env_3578_; lean_object* v_nextMacroScope_3579_; lean_object* v_ngen_3580_; lean_object* v_auxDeclNGen_3581_; lean_object* v_cache_3582_; lean_object* v_messages_3583_; lean_object* v_infoState_3584_; lean_object* v_snapshotTasks_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3615_; 
v___x_3576_ = lean_st_ref_take(v___y_3568_);
v_traceState_3577_ = lean_ctor_get(v___x_3576_, 4);
v_env_3578_ = lean_ctor_get(v___x_3576_, 0);
v_nextMacroScope_3579_ = lean_ctor_get(v___x_3576_, 1);
v_ngen_3580_ = lean_ctor_get(v___x_3576_, 2);
v_auxDeclNGen_3581_ = lean_ctor_get(v___x_3576_, 3);
v_cache_3582_ = lean_ctor_get(v___x_3576_, 5);
v_messages_3583_ = lean_ctor_get(v___x_3576_, 6);
v_infoState_3584_ = lean_ctor_get(v___x_3576_, 7);
v_snapshotTasks_3585_ = lean_ctor_get(v___x_3576_, 8);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3576_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3587_ = v___x_3576_;
v_isShared_3588_ = v_isSharedCheck_3615_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_snapshotTasks_3585_);
lean_inc(v_infoState_3584_);
lean_inc(v_messages_3583_);
lean_inc(v_cache_3582_);
lean_inc(v_traceState_3577_);
lean_inc(v_auxDeclNGen_3581_);
lean_inc(v_ngen_3580_);
lean_inc(v_nextMacroScope_3579_);
lean_inc(v_env_3578_);
lean_dec(v___x_3576_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3615_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
uint64_t v_tid_3589_; lean_object* v_traces_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3614_; 
v_tid_3589_ = lean_ctor_get_uint64(v_traceState_3577_, sizeof(void*)*1);
v_traces_3590_ = lean_ctor_get(v_traceState_3577_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v_traceState_3577_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3592_ = v_traceState_3577_;
v_isShared_3593_ = v_isSharedCheck_3614_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_traces_3590_);
lean_dec(v_traceState_3577_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3614_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; double v___x_3595_; uint8_t v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3604_; 
v___x_3594_ = lean_box(0);
v___x_3595_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__0, &l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__0);
v___x_3596_ = 0;
v___x_3597_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__1));
v___x_3598_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3598_, 0, v_cls_3565_);
lean_ctor_set(v___x_3598_, 1, v___x_3594_);
lean_ctor_set(v___x_3598_, 2, v___x_3597_);
lean_ctor_set_float(v___x_3598_, sizeof(void*)*3, v___x_3595_);
lean_ctor_set_float(v___x_3598_, sizeof(void*)*3 + 8, v___x_3595_);
lean_ctor_set_uint8(v___x_3598_, sizeof(void*)*3 + 16, v___x_3596_);
v___x_3599_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__6___closed__2));
v___x_3600_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3598_);
lean_ctor_set(v___x_3600_, 1, v_a_3572_);
lean_ctor_set(v___x_3600_, 2, v___x_3599_);
lean_inc(v_ref_3570_);
v___x_3601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3601_, 0, v_ref_3570_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
v___x_3602_ = l_Lean_PersistentArray_push___redArg(v_traces_3590_, v___x_3601_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v___x_3602_);
v___x_3604_ = v___x_3592_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3602_);
lean_ctor_set_uint64(v_reuseFailAlloc_3613_, sizeof(void*)*1, v_tid_3589_);
v___x_3604_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3606_; 
if (v_isShared_3588_ == 0)
{
lean_ctor_set(v___x_3587_, 4, v___x_3604_);
v___x_3606_ = v___x_3587_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v_env_3578_);
lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_nextMacroScope_3579_);
lean_ctor_set(v_reuseFailAlloc_3612_, 2, v_ngen_3580_);
lean_ctor_set(v_reuseFailAlloc_3612_, 3, v_auxDeclNGen_3581_);
lean_ctor_set(v_reuseFailAlloc_3612_, 4, v___x_3604_);
lean_ctor_set(v_reuseFailAlloc_3612_, 5, v_cache_3582_);
lean_ctor_set(v_reuseFailAlloc_3612_, 6, v_messages_3583_);
lean_ctor_set(v_reuseFailAlloc_3612_, 7, v_infoState_3584_);
lean_ctor_set(v_reuseFailAlloc_3612_, 8, v_snapshotTasks_3585_);
v___x_3606_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3607_ = lean_st_ref_set(v___y_3568_, v___x_3606_);
v___x_3608_ = lean_box(0);
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 0, v___x_3608_);
v___x_3610_ = v___x_3574_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_3617_, lean_object* v_msg_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v_res_3622_; 
v_res_3622_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__2(v_cls_3617_, v_msg_3618_, v___y_3619_, v___y_3620_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
return v_res_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(lean_object* v_mod_3623_, uint8_t v_isMeta_3624_, lean_object* v_hint_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v___x_3629_; lean_object* v_env_3630_; uint8_t v_isExporting_3631_; lean_object* v___x_3632_; lean_object* v_env_3633_; lean_object* v___x_3634_; lean_object* v_entry_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___y_3640_; lean_object* v___x_3665_; uint8_t v___x_3666_; 
v___x_3629_ = lean_st_ref_get(v___y_3627_);
v_env_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc_ref(v_env_3630_);
lean_dec(v___x_3629_);
v_isExporting_3631_ = lean_ctor_get_uint8(v_env_3630_, sizeof(void*)*8);
lean_dec_ref(v_env_3630_);
v___x_3632_ = lean_st_ref_get(v___y_3627_);
v_env_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc_ref(v_env_3633_);
lean_dec(v___x_3632_);
v___x_3634_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__2);
lean_inc(v_mod_3623_);
v_entry_3635_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3635_, 0, v_mod_3623_);
lean_ctor_set_uint8(v_entry_3635_, sizeof(void*)*1, v_isExporting_3631_);
lean_ctor_set_uint8(v_entry_3635_, sizeof(void*)*1 + 1, v_isMeta_3624_);
v___x_3636_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3637_ = lean_box(1);
v___x_3638_ = lean_box(0);
v___x_3665_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3634_, v___x_3636_, v_env_3633_, v___x_3637_, v___x_3638_);
v___x_3666_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3_spec__4___redArg(v___x_3665_, v_entry_3635_);
if (v___x_3666_ == 0)
{
lean_object* v_cls_3667_; lean_object* v___x_3668_; lean_object* v_a_3669_; lean_object* v___y_3671_; lean_object* v___y_3672_; lean_object* v___y_3676_; lean_object* v___y_3677_; uint8_t v___x_3689_; 
v_cls_3667_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__4));
v___x_3668_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___redArg(v_cls_3667_, v___y_3626_);
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_a_3669_);
lean_dec_ref(v___x_3668_);
v___x_3689_ = lean_unbox(v_a_3669_);
lean_dec(v_a_3669_);
if (v___x_3689_ == 0)
{
lean_dec(v_hint_3625_);
lean_dec(v_mod_3623_);
v___y_3640_ = v___y_3627_;
goto v___jp_3639_;
}
else
{
lean_object* v___x_3690_; lean_object* v___y_3692_; 
v___x_3690_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__11);
if (v_isExporting_3631_ == 0)
{
lean_object* v___x_3699_; 
v___x_3699_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__16));
v___y_3692_ = v___x_3699_;
goto v___jp_3691_;
}
else
{
lean_object* v___x_3700_; 
v___x_3700_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__17));
v___y_3692_ = v___x_3700_;
goto v___jp_3691_;
}
v___jp_3691_:
{
lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3693_ = l_Lean_stringToMessageData(v___y_3692_);
v___x_3694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3690_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
v___x_3695_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__13);
v___x_3696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3694_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
if (v_isMeta_3624_ == 0)
{
lean_object* v___x_3697_; 
v___x_3697_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__14));
v___y_3676_ = v___x_3696_;
v___y_3677_ = v___x_3697_;
goto v___jp_3675_;
}
else
{
lean_object* v___x_3698_; 
v___x_3698_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__15));
v___y_3676_ = v___x_3696_;
v___y_3677_ = v___x_3698_;
goto v___jp_3675_;
}
}
}
v___jp_3670_:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3673_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3673_, 0, v___y_3671_);
lean_ctor_set(v___x_3673_, 1, v___y_3672_);
v___x_3674_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__2(v_cls_3667_, v___x_3673_, v___y_3626_, v___y_3627_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_dec_ref(v___x_3674_);
v___y_3640_ = v___y_3627_;
goto v___jp_3639_;
}
else
{
lean_dec_ref(v_entry_3635_);
return v___x_3674_;
}
}
v___jp_3675_:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
v___x_3678_ = l_Lean_stringToMessageData(v___y_3677_);
v___x_3679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___y_3676_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
v___x_3680_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__6);
v___x_3681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3679_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
v___x_3682_ = l_Lean_MessageData_ofName(v_mod_3623_);
v___x_3683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3681_);
lean_ctor_set(v___x_3683_, 1, v___x_3682_);
v___x_3684_ = l_Lean_Name_isAnonymous(v_hint_3625_);
if (v___x_3684_ == 0)
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v___x_3685_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__8);
v___x_3686_ = l_Lean_MessageData_ofName(v_hint_3625_);
v___x_3687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3685_);
lean_ctor_set(v___x_3687_, 1, v___x_3686_);
v___y_3671_ = v___x_3683_;
v___y_3672_ = v___x_3687_;
goto v___jp_3670_;
}
else
{
lean_object* v___x_3688_; 
lean_dec(v_hint_3625_);
v___x_3688_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__3___closed__9);
v___y_3671_ = v___x_3683_;
v___y_3672_ = v___x_3688_;
goto v___jp_3670_;
}
}
}
else
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
lean_dec_ref(v_entry_3635_);
lean_dec(v_hint_3625_);
lean_dec(v_mod_3623_);
v___x_3701_ = lean_box(0);
v___x_3702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3701_);
return v___x_3702_;
}
v___jp_3639_:
{
lean_object* v___x_3641_; lean_object* v_toEnvExtension_3642_; lean_object* v_env_3643_; lean_object* v_nextMacroScope_3644_; lean_object* v_ngen_3645_; lean_object* v_auxDeclNGen_3646_; lean_object* v_traceState_3647_; lean_object* v_messages_3648_; lean_object* v_infoState_3649_; lean_object* v_snapshotTasks_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3663_; 
v___x_3641_ = lean_st_ref_take(v___y_3640_);
v_toEnvExtension_3642_ = lean_ctor_get(v___x_3636_, 0);
lean_inc_ref(v_toEnvExtension_3642_);
v_env_3643_ = lean_ctor_get(v___x_3641_, 0);
v_nextMacroScope_3644_ = lean_ctor_get(v___x_3641_, 1);
v_ngen_3645_ = lean_ctor_get(v___x_3641_, 2);
v_auxDeclNGen_3646_ = lean_ctor_get(v___x_3641_, 3);
v_traceState_3647_ = lean_ctor_get(v___x_3641_, 4);
v_messages_3648_ = lean_ctor_get(v___x_3641_, 6);
v_infoState_3649_ = lean_ctor_get(v___x_3641_, 7);
v_snapshotTasks_3650_ = lean_ctor_get(v___x_3641_, 8);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3663_ == 0)
{
lean_object* v_unused_3664_; 
v_unused_3664_ = lean_ctor_get(v___x_3641_, 5);
lean_dec(v_unused_3664_);
v___x_3652_ = v___x_3641_;
v_isShared_3653_ = v_isSharedCheck_3663_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_snapshotTasks_3650_);
lean_inc(v_infoState_3649_);
lean_inc(v_messages_3648_);
lean_inc(v_traceState_3647_);
lean_inc(v_auxDeclNGen_3646_);
lean_inc(v_ngen_3645_);
lean_inc(v_nextMacroScope_3644_);
lean_inc(v_env_3643_);
lean_dec(v___x_3641_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3663_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v_asyncMode_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3658_; 
v_asyncMode_3654_ = lean_ctor_get(v_toEnvExtension_3642_, 2);
lean_inc(v_asyncMode_3654_);
lean_dec_ref(v_toEnvExtension_3642_);
v___x_3655_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3636_, v_env_3643_, v_entry_3635_, v_asyncMode_3654_, v___x_3638_);
lean_dec(v_asyncMode_3654_);
v___x_3656_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_addCasesAttr_spec__0___redArg___closed__2);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 5, v___x_3656_);
lean_ctor_set(v___x_3652_, 0, v___x_3655_);
v___x_3658_ = v___x_3652_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_nextMacroScope_3644_);
lean_ctor_set(v_reuseFailAlloc_3662_, 2, v_ngen_3645_);
lean_ctor_set(v_reuseFailAlloc_3662_, 3, v_auxDeclNGen_3646_);
lean_ctor_set(v_reuseFailAlloc_3662_, 4, v_traceState_3647_);
lean_ctor_set(v_reuseFailAlloc_3662_, 5, v___x_3656_);
lean_ctor_set(v_reuseFailAlloc_3662_, 6, v_messages_3648_);
lean_ctor_set(v_reuseFailAlloc_3662_, 7, v_infoState_3649_);
lean_ctor_set(v_reuseFailAlloc_3662_, 8, v_snapshotTasks_3650_);
v___x_3658_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3659_ = lean_st_ref_set(v___y_3640_, v___x_3658_);
v___x_3660_ = lean_box(0);
v___x_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
return v___x_3661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0___boxed(lean_object* v_mod_3703_, lean_object* v_isMeta_3704_, lean_object* v_hint_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
uint8_t v_isMeta_boxed_3709_; lean_object* v_res_3710_; 
v_isMeta_boxed_3709_ = lean_unbox(v_isMeta_3704_);
v_res_3710_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_mod_3703_, v_isMeta_boxed_3709_, v_hint_3705_, v___y_3706_, v___y_3707_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(lean_object* v___x_3711_, lean_object* v_declName_3712_, lean_object* v_as_3713_, size_t v_sz_3714_, size_t v_i_3715_, lean_object* v_b_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
uint8_t v___x_3720_; 
v___x_3720_ = lean_usize_dec_lt(v_i_3715_, v_sz_3714_);
if (v___x_3720_ == 0)
{
lean_object* v___x_3721_; 
lean_dec(v_declName_3712_);
v___x_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3721_, 0, v_b_3716_);
return v___x_3721_;
}
else
{
lean_object* v___x_3722_; lean_object* v_modules_3723_; lean_object* v___x_3724_; lean_object* v_a_3725_; lean_object* v___x_3726_; lean_object* v_toImport_3727_; lean_object* v_module_3728_; uint8_t v___x_3729_; lean_object* v___x_3730_; 
v___x_3722_ = l_Lean_Environment_header(v___x_3711_);
v_modules_3723_ = lean_ctor_get(v___x_3722_, 3);
lean_inc_ref(v_modules_3723_);
lean_dec_ref(v___x_3722_);
v___x_3724_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3725_ = lean_array_uget_borrowed(v_as_3713_, v_i_3715_);
v___x_3726_ = lean_array_get(v___x_3724_, v_modules_3723_, v_a_3725_);
lean_dec_ref(v_modules_3723_);
v_toImport_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc_ref(v_toImport_3727_);
lean_dec(v___x_3726_);
v_module_3728_ = lean_ctor_get(v_toImport_3727_, 0);
lean_inc(v_module_3728_);
lean_dec_ref(v_toImport_3727_);
v___x_3729_ = 0;
lean_inc(v_declName_3712_);
v___x_3730_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3728_, v___x_3729_, v_declName_3712_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v___x_3731_; size_t v___x_3732_; size_t v___x_3733_; 
lean_dec_ref(v___x_3730_);
v___x_3731_ = lean_box(0);
v___x_3732_ = ((size_t)1ULL);
v___x_3733_ = lean_usize_add(v_i_3715_, v___x_3732_);
v_i_3715_ = v___x_3733_;
v_b_3716_ = v___x_3731_;
goto _start;
}
else
{
lean_dec(v_declName_3712_);
return v___x_3730_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1___boxed(lean_object* v___x_3735_, lean_object* v_declName_3736_, lean_object* v_as_3737_, lean_object* v_sz_3738_, lean_object* v_i_3739_, lean_object* v_b_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_){
_start:
{
size_t v_sz_boxed_3744_; size_t v_i_boxed_3745_; lean_object* v_res_3746_; 
v_sz_boxed_3744_ = lean_unbox_usize(v_sz_3738_);
lean_dec(v_sz_3738_);
v_i_boxed_3745_ = lean_unbox_usize(v_i_3739_);
lean_dec(v_i_3739_);
v_res_3746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v___x_3735_, v_declName_3736_, v_as_3737_, v_sz_boxed_3744_, v_i_boxed_3745_, v_b_3740_, v___y_3741_, v___y_3742_);
lean_dec(v___y_3742_);
lean_dec_ref(v___y_3741_);
lean_dec_ref(v_as_3737_);
lean_dec_ref(v___x_3735_);
return v_res_3746_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(lean_object* v_declName_3747_, uint8_t v_isMeta_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_){
_start:
{
lean_object* v___x_3752_; lean_object* v_env_3756_; lean_object* v___y_3758_; lean_object* v___x_3771_; 
v___x_3752_ = lean_st_ref_get(v___y_3750_);
v_env_3756_ = lean_ctor_get(v___x_3752_, 0);
lean_inc_ref(v_env_3756_);
lean_dec(v___x_3752_);
v___x_3771_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3756_, v_declName_3747_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_dec_ref(v_env_3756_);
lean_dec(v_declName_3747_);
goto v___jp_3753_;
}
else
{
lean_object* v_val_3772_; lean_object* v___x_3773_; lean_object* v_modules_3774_; lean_object* v___x_3775_; uint8_t v___x_3776_; 
v_val_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_val_3772_);
lean_dec_ref(v___x_3771_);
v___x_3773_ = l_Lean_Environment_header(v_env_3756_);
v_modules_3774_ = lean_ctor_get(v___x_3773_, 3);
lean_inc_ref(v_modules_3774_);
lean_dec_ref(v___x_3773_);
v___x_3775_ = lean_array_get_size(v_modules_3774_);
v___x_3776_ = lean_nat_dec_lt(v_val_3772_, v___x_3775_);
if (v___x_3776_ == 0)
{
lean_dec_ref(v_modules_3774_);
lean_dec(v_val_3772_);
lean_dec_ref(v_env_3756_);
lean_dec(v_declName_3747_);
goto v___jp_3753_;
}
else
{
lean_object* v___x_3777_; lean_object* v_env_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; uint8_t v___y_3782_; 
v___x_3777_ = lean_st_ref_get(v___y_3750_);
v_env_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc_ref(v_env_3778_);
lean_dec(v___x_3777_);
v___x_3779_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__2);
v___x_3780_ = lean_array_fget(v_modules_3774_, v_val_3772_);
lean_dec(v_val_3772_);
lean_dec_ref(v_modules_3774_);
if (v_isMeta_3748_ == 0)
{
lean_dec_ref(v_env_3778_);
v___y_3782_ = v_isMeta_3748_;
goto v___jp_3781_;
}
else
{
uint8_t v___x_3793_; 
lean_inc(v_declName_3747_);
v___x_3793_ = l_Lean_isMarkedMeta(v_env_3778_, v_declName_3747_);
if (v___x_3793_ == 0)
{
v___y_3782_ = v_isMeta_3748_;
goto v___jp_3781_;
}
else
{
uint8_t v___x_3794_; 
v___x_3794_ = 0;
v___y_3782_ = v___x_3794_;
goto v___jp_3781_;
}
}
v___jp_3781_:
{
lean_object* v_toImport_3783_; lean_object* v_module_3784_; lean_object* v___x_3785_; 
v_toImport_3783_ = lean_ctor_get(v___x_3780_, 0);
lean_inc_ref(v_toImport_3783_);
lean_dec(v___x_3780_);
v_module_3784_ = lean_ctor_get(v_toImport_3783_, 0);
lean_inc(v_module_3784_);
lean_dec_ref(v_toImport_3783_);
lean_inc(v_declName_3747_);
v___x_3785_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0(v_module_3784_, v___y_3782_, v_declName_3747_, v___y_3749_, v___y_3750_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; 
lean_dec_ref(v___x_3785_);
v___x_3786_ = l_Lean_indirectModUseExt;
v___x_3787_ = lean_box(1);
v___x_3788_ = lean_box(0);
lean_inc_ref(v_env_3756_);
v___x_3789_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3779_, v___x_3786_, v_env_3756_, v___x_3787_, v___x_3788_);
v___x_3790_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3789_, v_declName_3747_);
lean_dec(v___x_3789_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v___x_3791_; 
v___x_3791_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2___closed__3));
v___y_3758_ = v___x_3791_;
goto v___jp_3757_;
}
else
{
lean_object* v_val_3792_; 
v_val_3792_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_val_3792_);
lean_dec_ref(v___x_3790_);
v___y_3758_ = v_val_3792_;
goto v___jp_3757_;
}
}
else
{
lean_dec_ref(v_env_3756_);
lean_dec(v_declName_3747_);
return v___x_3785_;
}
}
}
}
v___jp_3753_:
{
lean_object* v___x_3754_; lean_object* v___x_3755_; 
v___x_3754_ = lean_box(0);
v___x_3755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3755_, 0, v___x_3754_);
return v___x_3755_;
}
v___jp_3757_:
{
lean_object* v___x_3759_; size_t v_sz_3760_; size_t v___x_3761_; lean_object* v___x_3762_; 
v___x_3759_ = lean_box(0);
v_sz_3760_ = lean_array_size(v___y_3758_);
v___x_3761_ = ((size_t)0ULL);
v___x_3762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__1(v_env_3756_, v_declName_3747_, v___y_3758_, v_sz_3760_, v___x_3761_, v___x_3759_, v___y_3749_, v___y_3750_);
lean_dec_ref(v___y_3758_);
lean_dec_ref(v_env_3756_);
if (lean_obj_tag(v___x_3762_) == 0)
{
lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3769_; 
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3762_);
if (v_isSharedCheck_3769_ == 0)
{
lean_object* v_unused_3770_; 
v_unused_3770_ = lean_ctor_get(v___x_3762_, 0);
lean_dec(v_unused_3770_);
v___x_3764_ = v___x_3762_;
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
else
{
lean_dec(v___x_3762_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v___x_3767_; 
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 0, v___x_3759_);
v___x_3767_ = v___x_3764_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v___x_3759_);
v___x_3767_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
return v___x_3767_;
}
}
}
else
{
return v___x_3762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0___boxed(lean_object* v_declName_3795_, lean_object* v_isMeta_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
uint8_t v_isMeta_boxed_3800_; lean_object* v_res_3801_; 
v_isMeta_boxed_3800_ = lean_unbox(v_isMeta_3796_);
v_res_3801_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_declName_3795_, v_isMeta_boxed_3800_, v___y_3797_, v___y_3798_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f(lean_object* v_attrName_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_){
_start:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3806_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3807_ = lean_st_ref_get(v___x_3806_);
v___x_3808_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr_spec__2_spec__5___redArg(v___x_3807_, v_attrName_3802_);
lean_dec(v___x_3807_);
if (lean_obj_tag(v___x_3808_) == 1)
{
lean_object* v_val_3809_; lean_object* v_ext_3810_; lean_object* v_name_3811_; uint8_t v___x_3812_; lean_object* v___x_3813_; 
v_val_3809_ = lean_ctor_get(v___x_3808_, 0);
lean_inc(v_val_3809_);
v_ext_3810_ = lean_ctor_get(v_val_3809_, 1);
lean_inc_ref(v_ext_3810_);
lean_dec(v_val_3809_);
v_name_3811_ = lean_ctor_get(v_ext_3810_, 1);
lean_inc(v_name_3811_);
lean_dec_ref(v_ext_3810_);
v___x_3812_ = 1;
v___x_3813_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0(v_name_3811_, v___x_3812_, v_a_3803_, v_a_3804_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3820_ == 0)
{
lean_object* v_unused_3821_; 
v_unused_3821_ = lean_ctor_get(v___x_3813_, 0);
lean_dec(v_unused_3821_);
v___x_3815_ = v___x_3813_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_dec(v___x_3813_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
lean_ctor_set(v___x_3815_, 0, v___x_3808_);
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3808_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec_ref(v___x_3808_);
v_a_3822_ = lean_ctor_get(v___x_3813_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3813_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3813_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3813_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
else
{
lean_object* v___x_3830_; 
v___x_3830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3808_);
return v___x_3830_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getExtension_x3f___boxed(lean_object* v_attrName_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_Lean_Meta_Grind_getExtension_x3f(v_attrName_3831_, v_a_3832_, v_a_3833_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
lean_dec(v_attrName_3831_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(lean_object* v_cls_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v___x_3840_; 
v___x_3840_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___redArg(v_cls_3836_, v___y_3837_);
return v___x_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_cls_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Meta_Grind_getExtension_x3f_spec__0_spec__0_spec__1(v_cls_3841_, v___y_3842_, v___y_3843_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
return v_res_3845_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_registerAttr___auto__1(void){
_start:
{
lean_object* v___x_3846_; 
v___x_3846_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25, &l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25_once, _init_l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___auto__1___closed__25);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_3847_, lean_object* v_x_3848_){
_start:
{
if (lean_obj_tag(v_x_3848_) == 0)
{
return v_x_3847_;
}
else
{
lean_object* v_key_3849_; lean_object* v_value_3850_; lean_object* v_tail_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3877_; 
v_key_3849_ = lean_ctor_get(v_x_3848_, 0);
v_value_3850_ = lean_ctor_get(v_x_3848_, 1);
v_tail_3851_ = lean_ctor_get(v_x_3848_, 2);
v_isSharedCheck_3877_ = !lean_is_exclusive(v_x_3848_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3853_ = v_x_3848_;
v_isShared_3854_ = v_isSharedCheck_3877_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_tail_3851_);
lean_inc(v_value_3850_);
lean_inc(v_key_3849_);
lean_dec(v_x_3848_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3877_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3855_; uint64_t v___y_3857_; 
v___x_3855_ = lean_array_get_size(v_x_3847_);
if (lean_obj_tag(v_key_3849_) == 0)
{
uint64_t v___x_3875_; 
v___x_3875_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_3857_ = v___x_3875_;
goto v___jp_3856_;
}
else
{
uint64_t v_hash_3876_; 
v_hash_3876_ = lean_ctor_get_uint64(v_key_3849_, sizeof(void*)*2);
v___y_3857_ = v_hash_3876_;
goto v___jp_3856_;
}
v___jp_3856_:
{
uint64_t v___x_3858_; uint64_t v___x_3859_; uint64_t v_fold_3860_; uint64_t v___x_3861_; uint64_t v___x_3862_; uint64_t v___x_3863_; size_t v___x_3864_; size_t v___x_3865_; size_t v___x_3866_; size_t v___x_3867_; size_t v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3871_; 
v___x_3858_ = 32ULL;
v___x_3859_ = lean_uint64_shift_right(v___y_3857_, v___x_3858_);
v_fold_3860_ = lean_uint64_xor(v___y_3857_, v___x_3859_);
v___x_3861_ = 16ULL;
v___x_3862_ = lean_uint64_shift_right(v_fold_3860_, v___x_3861_);
v___x_3863_ = lean_uint64_xor(v_fold_3860_, v___x_3862_);
v___x_3864_ = lean_uint64_to_usize(v___x_3863_);
v___x_3865_ = lean_usize_of_nat(v___x_3855_);
v___x_3866_ = ((size_t)1ULL);
v___x_3867_ = lean_usize_sub(v___x_3865_, v___x_3866_);
v___x_3868_ = lean_usize_land(v___x_3864_, v___x_3867_);
v___x_3869_ = lean_array_uget_borrowed(v_x_3847_, v___x_3868_);
lean_inc(v___x_3869_);
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 2, v___x_3869_);
v___x_3871_ = v___x_3853_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_key_3849_);
lean_ctor_set(v_reuseFailAlloc_3874_, 1, v_value_3850_);
lean_ctor_set(v_reuseFailAlloc_3874_, 2, v___x_3869_);
v___x_3871_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
lean_object* v___x_3872_; 
v___x_3872_ = lean_array_uset(v_x_3847_, v___x_3868_, v___x_3871_);
v_x_3847_ = v___x_3872_;
v_x_3848_ = v_tail_3851_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(lean_object* v_i_3878_, lean_object* v_source_3879_, lean_object* v_target_3880_){
_start:
{
lean_object* v___x_3881_; uint8_t v___x_3882_; 
v___x_3881_ = lean_array_get_size(v_source_3879_);
v___x_3882_ = lean_nat_dec_lt(v_i_3878_, v___x_3881_);
if (v___x_3882_ == 0)
{
lean_dec_ref(v_source_3879_);
lean_dec(v_i_3878_);
return v_target_3880_;
}
else
{
lean_object* v_es_3883_; lean_object* v___x_3884_; lean_object* v_source_3885_; lean_object* v_target_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; 
v_es_3883_ = lean_array_fget(v_source_3879_, v_i_3878_);
v___x_3884_ = lean_box(0);
v_source_3885_ = lean_array_fset(v_source_3879_, v_i_3878_, v___x_3884_);
v_target_3886_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_target_3880_, v_es_3883_);
v___x_3887_ = lean_unsigned_to_nat(1u);
v___x_3888_ = lean_nat_add(v_i_3878_, v___x_3887_);
lean_dec(v_i_3878_);
v_i_3878_ = v___x_3888_;
v_source_3879_ = v_source_3885_;
v_target_3880_ = v_target_3886_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(lean_object* v_data_3890_){
_start:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v_nbuckets_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3891_ = lean_array_get_size(v_data_3890_);
v___x_3892_ = lean_unsigned_to_nat(2u);
v_nbuckets_3893_ = lean_nat_mul(v___x_3891_, v___x_3892_);
v___x_3894_ = lean_unsigned_to_nat(0u);
v___x_3895_ = lean_box(0);
v___x_3896_ = lean_mk_array(v_nbuckets_3893_, v___x_3895_);
v___x_3897_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v___x_3894_, v_data_3890_, v___x_3896_);
return v___x_3897_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(lean_object* v_a_3898_, lean_object* v_x_3899_){
_start:
{
if (lean_obj_tag(v_x_3899_) == 0)
{
uint8_t v___x_3900_; 
v___x_3900_ = 0;
return v___x_3900_;
}
else
{
lean_object* v_key_3901_; lean_object* v_tail_3902_; uint8_t v___x_3903_; 
v_key_3901_ = lean_ctor_get(v_x_3899_, 0);
v_tail_3902_ = lean_ctor_get(v_x_3899_, 2);
v___x_3903_ = lean_name_eq(v_key_3901_, v_a_3898_);
if (v___x_3903_ == 0)
{
v_x_3899_ = v_tail_3902_;
goto _start;
}
else
{
return v___x_3903_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg___boxed(lean_object* v_a_3905_, lean_object* v_x_3906_){
_start:
{
uint8_t v_res_3907_; lean_object* v_r_3908_; 
v_res_3907_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3905_, v_x_3906_);
lean_dec(v_x_3906_);
lean_dec(v_a_3905_);
v_r_3908_ = lean_box(v_res_3907_);
return v_r_3908_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(lean_object* v_a_3909_, lean_object* v_b_3910_, lean_object* v_x_3911_){
_start:
{
if (lean_obj_tag(v_x_3911_) == 0)
{
lean_dec(v_b_3910_);
lean_dec(v_a_3909_);
return v_x_3911_;
}
else
{
lean_object* v_key_3912_; lean_object* v_value_3913_; lean_object* v_tail_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3926_; 
v_key_3912_ = lean_ctor_get(v_x_3911_, 0);
v_value_3913_ = lean_ctor_get(v_x_3911_, 1);
v_tail_3914_ = lean_ctor_get(v_x_3911_, 2);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_x_3911_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3916_ = v_x_3911_;
v_isShared_3917_ = v_isSharedCheck_3926_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_tail_3914_);
lean_inc(v_value_3913_);
lean_inc(v_key_3912_);
lean_dec(v_x_3911_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3926_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
uint8_t v___x_3918_; 
v___x_3918_ = lean_name_eq(v_key_3912_, v_a_3909_);
if (v___x_3918_ == 0)
{
lean_object* v___x_3919_; lean_object* v___x_3921_; 
v___x_3919_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3909_, v_b_3910_, v_tail_3914_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 2, v___x_3919_);
v___x_3921_ = v___x_3916_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_key_3912_);
lean_ctor_set(v_reuseFailAlloc_3922_, 1, v_value_3913_);
lean_ctor_set(v_reuseFailAlloc_3922_, 2, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
else
{
lean_object* v___x_3924_; 
lean_dec(v_value_3913_);
lean_dec(v_key_3912_);
if (v_isShared_3917_ == 0)
{
lean_ctor_set(v___x_3916_, 1, v_b_3910_);
lean_ctor_set(v___x_3916_, 0, v_a_3909_);
v___x_3924_ = v___x_3916_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3909_);
lean_ctor_set(v_reuseFailAlloc_3925_, 1, v_b_3910_);
lean_ctor_set(v_reuseFailAlloc_3925_, 2, v_tail_3914_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(lean_object* v_m_3927_, lean_object* v_a_3928_, lean_object* v_b_3929_){
_start:
{
lean_object* v_size_3930_; lean_object* v_buckets_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3977_; 
v_size_3930_ = lean_ctor_get(v_m_3927_, 0);
v_buckets_3931_ = lean_ctor_get(v_m_3927_, 1);
v_isSharedCheck_3977_ = !lean_is_exclusive(v_m_3927_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3933_ = v_m_3927_;
v_isShared_3934_ = v_isSharedCheck_3977_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_buckets_3931_);
lean_inc(v_size_3930_);
lean_dec(v_m_3927_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3977_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3935_; uint64_t v___y_3937_; 
v___x_3935_ = lean_array_get_size(v_buckets_3931_);
if (lean_obj_tag(v_a_3928_) == 0)
{
uint64_t v___x_3975_; 
v___x_3975_ = lean_uint64_once(&l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_Extension_isExtTheorem_spec__0___redArg___closed__0);
v___y_3937_ = v___x_3975_;
goto v___jp_3936_;
}
else
{
uint64_t v_hash_3976_; 
v_hash_3976_ = lean_ctor_get_uint64(v_a_3928_, sizeof(void*)*2);
v___y_3937_ = v_hash_3976_;
goto v___jp_3936_;
}
v___jp_3936_:
{
uint64_t v___x_3938_; uint64_t v___x_3939_; uint64_t v_fold_3940_; uint64_t v___x_3941_; uint64_t v___x_3942_; uint64_t v___x_3943_; size_t v___x_3944_; size_t v___x_3945_; size_t v___x_3946_; size_t v___x_3947_; size_t v___x_3948_; lean_object* v_bkt_3949_; uint8_t v___x_3950_; 
v___x_3938_ = 32ULL;
v___x_3939_ = lean_uint64_shift_right(v___y_3937_, v___x_3938_);
v_fold_3940_ = lean_uint64_xor(v___y_3937_, v___x_3939_);
v___x_3941_ = 16ULL;
v___x_3942_ = lean_uint64_shift_right(v_fold_3940_, v___x_3941_);
v___x_3943_ = lean_uint64_xor(v_fold_3940_, v___x_3942_);
v___x_3944_ = lean_uint64_to_usize(v___x_3943_);
v___x_3945_ = lean_usize_of_nat(v___x_3935_);
v___x_3946_ = ((size_t)1ULL);
v___x_3947_ = lean_usize_sub(v___x_3945_, v___x_3946_);
v___x_3948_ = lean_usize_land(v___x_3944_, v___x_3947_);
v_bkt_3949_ = lean_array_uget_borrowed(v_buckets_3931_, v___x_3948_);
v___x_3950_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_3928_, v_bkt_3949_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3951_; lean_object* v_size_x27_3952_; lean_object* v___x_3953_; lean_object* v_buckets_x27_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v___x_3951_ = lean_unsigned_to_nat(1u);
v_size_x27_3952_ = lean_nat_add(v_size_3930_, v___x_3951_);
lean_dec(v_size_3930_);
lean_inc(v_bkt_3949_);
v___x_3953_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3953_, 0, v_a_3928_);
lean_ctor_set(v___x_3953_, 1, v_b_3929_);
lean_ctor_set(v___x_3953_, 2, v_bkt_3949_);
v_buckets_x27_3954_ = lean_array_uset(v_buckets_3931_, v___x_3948_, v___x_3953_);
v___x_3955_ = lean_unsigned_to_nat(4u);
v___x_3956_ = lean_nat_mul(v_size_x27_3952_, v___x_3955_);
v___x_3957_ = lean_unsigned_to_nat(3u);
v___x_3958_ = lean_nat_div(v___x_3956_, v___x_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = lean_array_get_size(v_buckets_x27_3954_);
v___x_3960_ = lean_nat_dec_le(v___x_3958_, v___x_3959_);
lean_dec(v___x_3958_);
if (v___x_3960_ == 0)
{
lean_object* v_val_3961_; lean_object* v___x_3963_; 
v_val_3961_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_buckets_x27_3954_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 1, v_val_3961_);
lean_ctor_set(v___x_3933_, 0, v_size_x27_3952_);
v___x_3963_ = v___x_3933_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_size_x27_3952_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_val_3961_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
else
{
lean_object* v___x_3966_; 
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 1, v_buckets_x27_3954_);
lean_ctor_set(v___x_3933_, 0, v_size_x27_3952_);
v___x_3966_ = v___x_3933_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3967_; 
v_reuseFailAlloc_3967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_size_x27_3952_);
lean_ctor_set(v_reuseFailAlloc_3967_, 1, v_buckets_x27_3954_);
v___x_3966_ = v_reuseFailAlloc_3967_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
return v___x_3966_;
}
}
}
else
{
lean_object* v___x_3968_; lean_object* v_buckets_x27_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3973_; 
lean_inc(v_bkt_3949_);
v___x_3968_ = lean_box(0);
v_buckets_x27_3969_ = lean_array_uset(v_buckets_3931_, v___x_3948_, v___x_3968_);
v___x_3970_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_3928_, v_b_3929_, v_bkt_3949_);
v___x_3971_ = lean_array_uset(v_buckets_x27_3969_, v___x_3948_, v___x_3970_);
if (v_isShared_3934_ == 0)
{
lean_ctor_set(v___x_3933_, 1, v___x_3971_);
v___x_3973_ = v___x_3933_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_size_3930_);
lean_ctor_set(v_reuseFailAlloc_3974_, 1, v___x_3971_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr(lean_object* v_attrName_3978_, lean_object* v_ref_3979_){
_start:
{
lean_object* v___x_3981_; 
lean_inc(v_ref_3979_);
v___x_3981_ = l_Lean_Meta_Grind_mkExtension(v_ref_3979_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; uint8_t v___x_3983_; uint8_t v___x_3984_; lean_object* v___x_3985_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_a_3982_);
lean_dec_ref(v___x_3981_);
v___x_3983_ = 0;
v___x_3984_ = 1;
lean_inc(v_ref_3979_);
lean_inc(v_a_3982_);
lean_inc(v_attrName_3978_);
v___x_3985_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3978_, v___x_3983_, v___x_3984_, v_a_3982_, v_ref_3979_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v___x_3986_; 
lean_dec_ref(v___x_3985_);
lean_inc(v_ref_3979_);
lean_inc(v_a_3982_);
lean_inc(v_attrName_3978_);
v___x_3986_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3978_, v___x_3983_, v___x_3983_, v_a_3982_, v_ref_3979_);
if (lean_obj_tag(v___x_3986_) == 0)
{
lean_object* v___x_3987_; 
lean_dec_ref(v___x_3986_);
lean_inc(v_ref_3979_);
lean_inc(v_a_3982_);
lean_inc(v_attrName_3978_);
v___x_3987_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3978_, v___x_3984_, v___x_3984_, v_a_3982_, v_ref_3979_);
if (lean_obj_tag(v___x_3987_) == 0)
{
lean_object* v___x_3988_; 
lean_dec_ref(v___x_3987_);
lean_inc(v_a_3982_);
lean_inc(v_attrName_3978_);
v___x_3988_ = l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr(v_attrName_3978_, v___x_3984_, v___x_3983_, v_a_3982_, v_ref_3979_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3999_; 
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_3999_ == 0)
{
lean_object* v_unused_4000_; 
v_unused_4000_ = lean_ctor_get(v___x_3988_, 0);
lean_dec(v_unused_4000_);
v___x_3990_ = v___x_3988_;
v_isShared_3991_ = v_isSharedCheck_3999_;
goto v_resetjp_3989_;
}
else
{
lean_dec(v___x_3988_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3999_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3997_; 
v___x_3992_ = l_Lean_Meta_Grind_extensionMapRef;
v___x_3993_ = lean_st_ref_take(v___x_3992_);
lean_inc(v_a_3982_);
v___x_3994_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v___x_3993_, v_attrName_3978_, v_a_3982_);
v___x_3995_ = lean_st_ref_set(v___x_3992_, v___x_3994_);
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 0, v_a_3982_);
v___x_3997_ = v___x_3990_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3982_);
v___x_3997_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
return v___x_3997_;
}
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_dec(v_a_3982_);
lean_dec(v_attrName_3978_);
v_a_4001_ = lean_ctor_get(v___x_3988_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3988_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3988_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3988_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
else
{
lean_object* v_a_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4016_; 
lean_dec(v_a_3982_);
lean_dec(v_ref_3979_);
lean_dec(v_attrName_3978_);
v_a_4009_ = lean_ctor_get(v___x_3987_, 0);
v_isSharedCheck_4016_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4016_ == 0)
{
v___x_4011_ = v___x_3987_;
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_a_4009_);
lean_dec(v___x_3987_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4016_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4014_; 
if (v_isShared_4012_ == 0)
{
v___x_4014_ = v___x_4011_;
goto v_reusejp_4013_;
}
else
{
lean_object* v_reuseFailAlloc_4015_; 
v_reuseFailAlloc_4015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4015_, 0, v_a_4009_);
v___x_4014_ = v_reuseFailAlloc_4015_;
goto v_reusejp_4013_;
}
v_reusejp_4013_:
{
return v___x_4014_;
}
}
}
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
lean_dec(v_a_3982_);
lean_dec(v_ref_3979_);
lean_dec(v_attrName_3978_);
v_a_4017_ = lean_ctor_get(v___x_3986_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_3986_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_3986_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_3986_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
else
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
lean_dec(v_a_3982_);
lean_dec(v_ref_3979_);
lean_dec(v_attrName_3978_);
v_a_4025_ = lean_ctor_get(v___x_3985_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_3985_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___x_3985_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_3985_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
else
{
lean_dec(v_ref_3979_);
lean_dec(v_attrName_3978_);
return v___x_3981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_registerAttr___boxed(lean_object* v_attrName_4033_, lean_object* v_ref_4034_, lean_object* v_a_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Lean_Meta_Grind_registerAttr(v_attrName_4033_, v_ref_4034_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0(lean_object* v_00_u03b2_4037_, lean_object* v_m_4038_, lean_object* v_a_4039_, lean_object* v_b_4040_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0___redArg(v_m_4038_, v_a_4039_, v_b_4040_);
return v___x_4041_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(lean_object* v_00_u03b2_4042_, lean_object* v_a_4043_, lean_object* v_x_4044_){
_start:
{
uint8_t v___x_4045_; 
v___x_4045_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___redArg(v_a_4043_, v_x_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0___boxed(lean_object* v_00_u03b2_4046_, lean_object* v_a_4047_, lean_object* v_x_4048_){
_start:
{
uint8_t v_res_4049_; lean_object* v_r_4050_; 
v_res_4049_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__0(v_00_u03b2_4046_, v_a_4047_, v_x_4048_);
lean_dec(v_x_4048_);
lean_dec(v_a_4047_);
v_r_4050_ = lean_box(v_res_4049_);
return v_r_4050_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1(lean_object* v_00_u03b2_4051_, lean_object* v_data_4052_){
_start:
{
lean_object* v___x_4053_; 
v___x_4053_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1___redArg(v_data_4052_);
return v___x_4053_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2(lean_object* v_00_u03b2_4054_, lean_object* v_a_4055_, lean_object* v_b_4056_, lean_object* v_x_4057_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__2___redArg(v_a_4055_, v_b_4056_, v_x_4057_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_4059_, lean_object* v_i_4060_, lean_object* v_source_4061_, lean_object* v_target_4062_){
_start:
{
lean_object* v___x_4063_; 
v___x_4063_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2___redArg(v_i_4060_, v_source_4061_, v_target_4062_);
return v___x_4063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_4064_, lean_object* v_x_4065_, lean_object* v_x_4066_){
_start:
{
lean_object* v___x_4067_; 
v___x_4067_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Grind_registerAttr_spec__0_spec__1_spec__2_spec__3___redArg(v_x_4065_, v_x_4066_);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4074_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Attr_0__Lean_Meta_Grind_mkGrindAttr___lam__2___closed__9));
v___x_4075_ = ((lean_object*)(l_Lean_Meta_Grind_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_));
v___x_4076_ = l_Lean_Meta_Grind_registerAttr(v___x_4074_, v___x_4075_);
return v___x_4076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2____boxed(lean_object* v_a_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg(lean_object* v_declName_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v___x_4082_; lean_object* v_env_4083_; lean_object* v___x_4084_; lean_object* v_ext_4085_; lean_object* v_toEnvExtension_4086_; lean_object* v_asyncMode_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v_casesTypes_4090_; uint8_t v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; 
v___x_4082_ = lean_st_ref_get(v_a_4080_);
v_env_4083_ = lean_ctor_get(v___x_4082_, 0);
lean_inc_ref(v_env_4083_);
lean_dec(v___x_4082_);
v___x_4084_ = l_Lean_Meta_Grind_grindExt;
v_ext_4085_ = lean_ctor_get(v___x_4084_, 1);
lean_inc_ref(v_ext_4085_);
v_toEnvExtension_4086_ = lean_ctor_get(v_ext_4085_, 0);
lean_inc_ref(v_toEnvExtension_4086_);
lean_dec_ref(v_ext_4085_);
v_asyncMode_4087_ = lean_ctor_get(v_toEnvExtension_4086_, 2);
lean_inc(v_asyncMode_4087_);
lean_dec_ref(v_toEnvExtension_4086_);
v___x_4088_ = l_Lean_Meta_Grind_instInhabitedExtensionState_default;
v___x_4089_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4088_, v___x_4084_, v_env_4083_, v_asyncMode_4087_);
lean_dec(v_asyncMode_4087_);
v_casesTypes_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc_ref(v_casesTypes_4090_);
lean_dec(v___x_4089_);
v___x_4091_ = l_Lean_Meta_Grind_CasesTypes_isSplit(v_casesTypes_4090_, v_declName_4079_);
v___x_4092_ = lean_box(v___x_4091_);
v___x_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4093_, 0, v___x_4092_);
return v___x_4093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___redArg___boxed(lean_object* v_declName_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4094_, v_a_4095_);
lean_dec(v_a_4095_);
lean_dec(v_declName_4094_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit(lean_object* v_declName_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_){
_start:
{
lean_object* v___x_4102_; 
v___x_4102_ = l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4098_, v_a_4100_);
return v___x_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isGlobalSplit___boxed(lean_object* v_declName_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l_Lean_Meta_Grind_isGlobalSplit(v_declName_4103_, v_a_4104_, v_a_4105_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
lean_dec(v_declName_4103_);
return v_res_4107_;
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
res = l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_2724751884____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_normExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_normExt);
lean_dec_ref(res);
res = l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_420965636____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Grind_extensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Grind_extensionMapRef);
lean_dec_ref(res);
res = l_Lean_Meta_Grind_initFn_00___x40_Lean_Meta_Tactic_Grind_Attr_793357512____hygCtx___hyg_2_();
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
