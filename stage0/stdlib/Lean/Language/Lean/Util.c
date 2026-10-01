// Lean compiler output
// Module: Lean.Language.Lean.Util
// Imports: public import Lean.Language.Lean.Types import Lean.Elab.InfoTree.Util
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
lean_object* l_Lean_Elab_Info_range_x3f(lean_object*);
uint8_t l_Lean_Syntax_Range_overlaps(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Language_SnapshotTree_transform___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_transformWith___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object*, uint8_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
lean_object* l_Lean_Language_Snapshot_transform(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
extern lean_object* l_Lean_MessageLog_empty;
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeContainsHoverPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeContainsHoverPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeOverlapsRequestedRange(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeOverlapsRequestedRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeIncludesRequestedRange(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeIncludesRequestedRange___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 1}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1 = (const lean_object*)&l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdParsedSnap___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdParsedSnap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Language_Lean_findCmdDataAtPos_spec__0(lean_object*);
static const lean_string_object l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Language.Lean.Util"};
static const lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__0 = (const lean_object*)&l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__0_value;
static const lean_string_object l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Lean.Language.Lean.findCmdDataAtPos"};
static const lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__1 = (const lean_object*)&l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__1_value;
static const lean_string_object l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: s.infoTree\?.isSome\n        "};
static const lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__2 = (const lean_object*)&l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTree_transform___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1(lean_object*);
static lean_once_cell_t l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__2(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos___lam__0(lean_object*);
static const lean_closure_object l_Lean_Language_Lean_findInfoTreeAtPos___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_findInfoTreeAtPos___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Language_Lean_findInfoTreeAtPos___closed__0 = (const lean_object*)&l_Lean_Language_Lean_findInfoTreeAtPos___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeContainsHoverPos(lean_object* v_text_1_, lean_object* v_r_2_, lean_object* v_hoverPos_3_, uint8_t v_includeStop_4_){
_start:
{
if (v_includeStop_4_ == 0)
{
lean_object* v_stop_5_; lean_object* v_source_6_; lean_object* v___x_7_; uint8_t v_decide_8_; uint8_t v___x_9_; 
v_stop_5_ = lean_ctor_get(v_r_2_, 1);
v_source_6_ = lean_ctor_get(v_text_1_, 0);
v___x_7_ = lean_string_utf8_byte_size(v_source_6_);
v_decide_8_ = lean_nat_dec_eq(v_stop_5_, v___x_7_);
v___x_9_ = l_Lean_Syntax_Range_contains(v_r_2_, v_hoverPos_3_, v_decide_8_);
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = l_Lean_Syntax_Range_contains(v_r_2_, v_hoverPos_3_, v_includeStop_4_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeContainsHoverPos___boxed(lean_object* v_text_11_, lean_object* v_r_12_, lean_object* v_hoverPos_13_, lean_object* v_includeStop_14_){
_start:
{
uint8_t v_includeStop_boxed_15_; uint8_t v_res_16_; lean_object* v_r_17_; 
v_includeStop_boxed_15_ = lean_unbox(v_includeStop_14_);
v_res_16_ = l_Lean_FileMap_rangeContainsHoverPos(v_text_11_, v_r_12_, v_hoverPos_13_, v_includeStop_boxed_15_);
lean_dec(v_hoverPos_13_);
lean_dec_ref(v_r_12_);
lean_dec_ref(v_text_11_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeOverlapsRequestedRange(lean_object* v_text_18_, lean_object* v_documentRange_19_, lean_object* v_requestedRange_20_, uint8_t v_includeDocumentRangeStop_21_, uint8_t v_includeRequestedRangeStop_22_){
_start:
{
if (v_includeDocumentRangeStop_21_ == 0)
{
lean_object* v_stop_23_; lean_object* v_source_24_; lean_object* v___x_25_; uint8_t v_decide_26_; uint8_t v___x_27_; 
v_stop_23_ = lean_ctor_get(v_documentRange_19_, 1);
v_source_24_ = lean_ctor_get(v_text_18_, 0);
v___x_25_ = lean_string_utf8_byte_size(v_source_24_);
v_decide_26_ = lean_nat_dec_eq(v_stop_23_, v___x_25_);
v___x_27_ = l_Lean_Syntax_Range_overlaps(v_documentRange_19_, v_requestedRange_20_, v_decide_26_, v_includeRequestedRangeStop_22_);
return v___x_27_;
}
else
{
uint8_t v___x_28_; 
v___x_28_ = l_Lean_Syntax_Range_overlaps(v_documentRange_19_, v_requestedRange_20_, v_includeDocumentRangeStop_21_, v_includeRequestedRangeStop_22_);
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeOverlapsRequestedRange___boxed(lean_object* v_text_29_, lean_object* v_documentRange_30_, lean_object* v_requestedRange_31_, lean_object* v_includeDocumentRangeStop_32_, lean_object* v_includeRequestedRangeStop_33_){
_start:
{
uint8_t v_includeDocumentRangeStop_boxed_34_; uint8_t v_includeRequestedRangeStop_boxed_35_; uint8_t v_res_36_; lean_object* v_r_37_; 
v_includeDocumentRangeStop_boxed_34_ = lean_unbox(v_includeDocumentRangeStop_32_);
v_includeRequestedRangeStop_boxed_35_ = lean_unbox(v_includeRequestedRangeStop_33_);
v_res_36_ = l_Lean_FileMap_rangeOverlapsRequestedRange(v_text_29_, v_documentRange_30_, v_requestedRange_31_, v_includeDocumentRangeStop_boxed_34_, v_includeRequestedRangeStop_boxed_35_);
lean_dec_ref(v_requestedRange_31_);
lean_dec_ref(v_documentRange_30_);
lean_dec_ref(v_text_29_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
LEAN_EXPORT uint8_t l_Lean_FileMap_rangeIncludesRequestedRange(lean_object* v_text_38_, lean_object* v_documentRange_39_, lean_object* v_requestedRange_40_, uint8_t v_includeDocumentRangeStop_41_, uint8_t v_includeRequestedRangeStop_42_){
_start:
{
if (v_includeDocumentRangeStop_41_ == 0)
{
lean_object* v_stop_43_; lean_object* v_source_44_; lean_object* v___x_45_; uint8_t v_decide_46_; uint8_t v___x_47_; 
v_stop_43_ = lean_ctor_get(v_documentRange_39_, 1);
v_source_44_ = lean_ctor_get(v_text_38_, 0);
v___x_45_ = lean_string_utf8_byte_size(v_source_44_);
v_decide_46_ = lean_nat_dec_eq(v_stop_43_, v___x_45_);
v___x_47_ = l_Lean_Syntax_Range_includes(v_documentRange_39_, v_requestedRange_40_, v_decide_46_, v_includeRequestedRangeStop_42_);
return v___x_47_;
}
else
{
uint8_t v___x_48_; 
v___x_48_ = l_Lean_Syntax_Range_includes(v_documentRange_39_, v_requestedRange_40_, v_includeDocumentRangeStop_41_, v_includeRequestedRangeStop_42_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_FileMap_rangeIncludesRequestedRange___boxed(lean_object* v_text_49_, lean_object* v_documentRange_50_, lean_object* v_requestedRange_51_, lean_object* v_includeDocumentRangeStop_52_, lean_object* v_includeRequestedRangeStop_53_){
_start:
{
uint8_t v_includeDocumentRangeStop_boxed_54_; uint8_t v_includeRequestedRangeStop_boxed_55_; uint8_t v_res_56_; lean_object* v_r_57_; 
v_includeDocumentRangeStop_boxed_54_ = lean_unbox(v_includeDocumentRangeStop_52_);
v_includeRequestedRangeStop_boxed_55_ = lean_unbox(v_includeRequestedRangeStop_53_);
v_res_56_ = l_Lean_FileMap_rangeIncludesRequestedRange(v_text_49_, v_documentRange_50_, v_requestedRange_51_, v_includeDocumentRangeStop_boxed_54_, v_includeRequestedRangeStop_boxed_55_);
lean_dec_ref(v_requestedRange_51_);
lean_dec_ref(v_documentRange_50_);
lean_dec_ref(v_text_49_);
v_r_57_ = lean_box(v_res_56_);
return v_r_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx(lean_object* v_x_58_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_object* v___x_59_; 
v___x_59_ = lean_unsigned_to_nat(0u);
return v___x_59_;
}
else
{
lean_object* v___x_60_; 
v___x_60_ = lean_unsigned_to_nat(1u);
return v___x_60_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx___boxed(lean_object* v_x_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorIdx(v_x_61_);
lean_dec(v_x_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(lean_object* v_t_63_, lean_object* v_k_64_){
_start:
{
if (lean_obj_tag(v_t_63_) == 0)
{
return v_k_64_;
}
else
{
uint8_t v_foldChildren_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v_foldChildren_65_ = lean_ctor_get_uint8(v_t_63_, 0);
v___x_66_ = lean_box(v_foldChildren_65_);
v___x_67_ = lean_apply_1(v_k_64_, v___x_66_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg___boxed(lean_object* v_t_68_, lean_object* v_k_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_68_, v_k_69_);
lean_dec(v_t_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim(lean_object* v_motive_71_, lean_object* v_ctorIdx_72_, lean_object* v_t_73_, lean_object* v_h_74_, lean_object* v_k_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_73_, v_k_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___boxed(lean_object* v_motive_77_, lean_object* v_ctorIdx_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_k_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim(v_motive_77_, v_ctorIdx_78_, v_t_79_, v_h_80_, v_k_81_);
lean_dec(v_t_79_);
lean_dec(v_ctorIdx_78_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg(lean_object* v_t_83_, lean_object* v_done_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_83_, v_done_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg___boxed(lean_object* v_t_86_, lean_object* v_done_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___redArg(v_t_86_, v_done_87_);
lean_dec(v_t_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim(lean_object* v_motive_89_, lean_object* v_t_90_, lean_object* v_h_91_, lean_object* v_done_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_90_, v_done_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim___boxed(lean_object* v_motive_94_, lean_object* v_t_95_, lean_object* v_h_96_, lean_object* v_done_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_done_elim(v_motive_94_, v_t_95_, v_h_96_, v_done_97_);
lean_dec(v_t_95_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg(lean_object* v_t_99_, lean_object* v_proceed_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_99_, v_proceed_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg___boxed(lean_object* v_t_102_, lean_object* v_proceed_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___redArg(v_t_102_, v_proceed_103_);
lean_dec(v_t_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim(lean_object* v_motive_105_, lean_object* v_t_106_, lean_object* v_h_107_, lean_object* v_proceed_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_ctorElim___redArg(v_t_106_, v_proceed_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim___boxed(lean_object* v_motive_110_, lean_object* v_t_111_, lean_object* v_h_112_, lean_object* v_proceed_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_Language_SnapshotTree_foldSnaps_Control_proceed_elim(v_motive_110_, v_t_111_, v_h_112_, v_proceed_113_);
lean_dec(v_t_111_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__0(lean_object* v_f_115_, lean_object* v_tail_116_, lean_object* v_x_117_){
_start:
{
lean_object* v_snd_118_; uint8_t v___x_119_; 
v_snd_118_ = lean_ctor_get(v_x_117_, 1);
v___x_119_ = lean_unbox(v_snd_118_);
if (v___x_119_ == 0)
{
lean_object* v_fst_120_; lean_object* v___x_121_; 
v_fst_120_ = lean_ctor_get(v_x_117_, 0);
lean_inc(v_fst_120_);
lean_dec_ref(v_x_117_);
v___x_121_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_115_, v_fst_120_, v_tail_116_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; 
lean_dec(v_tail_116_);
lean_dec_ref(v_f_115_);
v___x_122_ = lean_task_pure(v_x_117_);
return v___x_122_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__2(lean_object* v_f_123_, lean_object* v_tail_124_, lean_object* v_head_125_, lean_object* v___f_126_, lean_object* v_x_127_){
_start:
{
lean_object* v_snd_128_; 
v_snd_128_ = lean_ctor_get(v_x_127_, 1);
if (lean_obj_tag(v_snd_128_) == 1)
{
uint8_t v_foldChildren_129_; 
v_foldChildren_129_ = lean_ctor_get_uint8(v_snd_128_, 0);
if (v_foldChildren_129_ == 0)
{
lean_object* v_fst_130_; lean_object* v___x_131_; 
lean_dec_ref(v___f_126_);
lean_dec_ref(v_head_125_);
v_fst_130_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_fst_130_);
lean_dec_ref(v_x_127_);
v___x_131_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_123_, v_fst_130_, v_tail_124_);
return v___x_131_;
}
else
{
lean_object* v_fst_132_; lean_object* v_task_133_; lean_object* v___f_134_; lean_object* v___x_135_; lean_object* v_subtreeTask_136_; lean_object* v___x_137_; 
lean_dec(v_tail_124_);
v_fst_132_ = lean_ctor_get(v_x_127_, 0);
lean_inc(v_fst_132_);
lean_dec_ref(v_x_127_);
v_task_133_ = lean_ctor_get(v_head_125_, 3);
lean_inc_ref(v_task_133_);
lean_dec_ref(v_head_125_);
v___f_134_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__1), 3, 2);
lean_closure_set(v___f_134_, 0, v_f_123_);
lean_closure_set(v___f_134_, 1, v_fst_132_);
v___x_135_ = lean_unsigned_to_nat(0u);
v_subtreeTask_136_ = lean_task_bind(v_task_133_, v___f_134_, v___x_135_, v_foldChildren_129_);
v___x_137_ = lean_task_bind(v_subtreeTask_136_, v___f_126_, v___x_135_, v_foldChildren_129_);
return v___x_137_;
}
}
else
{
lean_object* v_fst_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_148_; 
lean_dec_ref(v___f_126_);
lean_dec_ref(v_head_125_);
lean_dec(v_tail_124_);
lean_dec_ref(v_f_123_);
v_fst_138_ = lean_ctor_get(v_x_127_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v_x_127_);
if (v_isSharedCheck_148_ == 0)
{
lean_object* v_unused_149_; 
v_unused_149_ = lean_ctor_get(v_x_127_, 1);
lean_dec(v_unused_149_);
v___x_140_ = v_x_127_;
v_isShared_141_ = v_isSharedCheck_148_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_fst_138_);
lean_dec(v_x_127_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_148_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_142_ = 1;
v___x_143_ = lean_box(v___x_142_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 1, v___x_143_);
v___x_145_ = v___x_140_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_fst_138_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___x_143_);
v___x_145_ = v_reuseFailAlloc_147_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_146_; 
v___x_146_ = lean_task_pure(v___x_145_);
return v___x_146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(lean_object* v_f_150_, lean_object* v_acc_151_, lean_object* v_a_152_){
_start:
{
if (lean_obj_tag(v_a_152_) == 0)
{
uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec_ref(v_f_150_);
v___x_153_ = 0;
v___x_154_ = lean_box(v___x_153_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v_acc_151_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = lean_task_pure(v___x_155_);
return v___x_156_;
}
else
{
lean_object* v_head_157_; lean_object* v_tail_158_; lean_object* v___f_159_; lean_object* v___f_160_; lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; lean_object* v___x_164_; 
v_head_157_ = lean_ctor_get(v_a_152_, 0);
lean_inc_n(v_head_157_, 2);
v_tail_158_ = lean_ctor_get(v_a_152_, 1);
lean_inc_n(v_tail_158_, 2);
lean_dec_ref_known(v_a_152_, 2);
lean_inc_ref_n(v_f_150_, 2);
v___f_159_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__0), 3, 2);
lean_closure_set(v___f_159_, 0, v_f_150_);
lean_closure_set(v___f_159_, 1, v_tail_158_);
v___f_160_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__2), 5, 4);
lean_closure_set(v___f_160_, 0, v_f_150_);
lean_closure_set(v___f_160_, 1, v_tail_158_);
lean_closure_set(v___f_160_, 2, v_head_157_);
lean_closure_set(v___f_160_, 3, v___f_159_);
v___x_161_ = lean_apply_2(v_f_150_, v_head_157_, v_acc_151_);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = 1;
v___x_164_ = lean_task_bind(v___x_161_, v___f_160_, v___x_162_, v___x_163_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(lean_object* v_f_165_, lean_object* v_acc_166_, lean_object* v_tree_167_){
_start:
{
lean_object* v_children_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_children_168_ = lean_ctor_get(v_tree_167_, 1);
lean_inc_ref(v_children_168_);
lean_dec_ref(v_tree_167_);
v___x_169_ = lean_array_to_list(v_children_168_);
v___x_170_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_165_, v_acc_166_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg___lam__1(lean_object* v_f_171_, lean_object* v_fst_172_, lean_object* v_tree_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(v_f_171_, v_fst_172_, v_tree_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree(lean_object* v_00_u03b1_175_, lean_object* v_f_176_, lean_object* v_acc_177_, lean_object* v_tree_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(v_f_176_, v_acc_177_, v_tree_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren(lean_object* v_00_u03b1_180_, lean_object* v_f_181_, lean_object* v_acc_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseChildren___redArg(v_f_181_, v_acc_182_, v_a_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0(lean_object* v_x_185_){
_start:
{
lean_object* v_fst_186_; 
v_fst_186_ = lean_ctor_get(v_x_185_, 0);
lean_inc(v_fst_186_);
return v_fst_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0___boxed(lean_object* v_x_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg___lam__0(v_x_187_);
lean_dec_ref(v_x_187_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps___redArg(lean_object* v_tree_190_, lean_object* v_init_191_, lean_object* v_f_192_){
_start:
{
lean_object* v___f_193_; lean_object* v_t_194_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; 
v___f_193_ = ((lean_object*)(l_Lean_Language_SnapshotTree_foldSnaps___redArg___closed__0));
v_t_194_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_SnapshotTree_foldSnaps_traverseTree___redArg(v_f_192_, v_init_191_, v_tree_190_);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = 1;
v___x_197_ = lean_task_map(v___f_193_, v_t_194_, v___x_195_, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldSnaps(lean_object* v_00_u03b1_198_, lean_object* v_tree_199_, lean_object* v_init_200_, lean_object* v_f_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_199_, v_init_200_, v_f_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(uint8_t v___x_203_, lean_object* v___x_204_, lean_object* v_tree_205_){
_start:
{
lean_object* v_element_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_219_; 
v_element_206_ = lean_ctor_get(v_tree_205_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v_tree_205_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; 
v_unused_220_ = lean_ctor_get(v_tree_205_, 1);
lean_dec(v_unused_220_);
v___x_208_ = v_tree_205_;
v_isShared_209_ = v_isSharedCheck_219_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_element_206_);
lean_dec(v_tree_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_219_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v_infoTree_x3f_210_; 
v_infoTree_x3f_210_ = lean_ctor_get(v_element_206_, 2);
lean_inc(v_infoTree_x3f_210_);
lean_dec_ref(v_element_206_);
if (lean_obj_tag(v_infoTree_x3f_210_) == 1)
{
lean_object* v___x_211_; lean_object* v___x_213_; 
lean_dec(v___x_204_);
v___x_211_ = lean_box(0);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_211_);
lean_ctor_set(v___x_208_, 0, v_infoTree_x3f_210_);
v___x_213_ = v___x_208_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_infoTree_x3f_210_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
else
{
lean_object* v___x_215_; lean_object* v___x_217_; 
lean_dec(v_infoTree_x3f_210_);
v___x_215_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_215_, 0, v___x_203_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 1, v___x_215_);
lean_ctor_set(v___x_208_, 0, v___x_204_);
v___x_217_ = v___x_208_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v___x_215_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0___boxed(lean_object* v___x_221_, lean_object* v___x_222_, lean_object* v_tree_223_){
_start:
{
uint8_t v___x_408__boxed_224_; lean_object* v_res_225_; 
v___x_408__boxed_224_ = lean_unbox(v___x_221_);
v_res_225_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0(v___x_408__boxed_224_, v___x_222_, v_tree_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(lean_object* v_text_230_, lean_object* v_hoverPos_231_, uint8_t v_includeStop_232_, lean_object* v___x_233_, lean_object* v_snap_234_, lean_object* v_x_235_){
_start:
{
lean_object* v_stx_x3f_236_; 
v_stx_x3f_236_ = lean_ctor_get(v_snap_234_, 0);
lean_inc(v_stx_x3f_236_);
if (lean_obj_tag(v_stx_x3f_236_) == 1)
{
lean_object* v_task_237_; lean_object* v_val_238_; uint8_t v___x_239_; lean_object* v___x_240_; 
v_task_237_ = lean_ctor_get(v_snap_234_, 3);
lean_inc_ref(v_task_237_);
lean_dec_ref(v_snap_234_);
v_val_238_ = lean_ctor_get(v_stx_x3f_236_, 0);
lean_inc(v_val_238_);
lean_dec_ref_known(v_stx_x3f_236_, 1);
v___x_239_ = 1;
v___x_240_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_238_, v___x_239_);
lean_dec(v_val_238_);
if (lean_obj_tag(v___x_240_) == 1)
{
lean_object* v_val_241_; uint8_t v___x_242_; 
v_val_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_val_241_);
lean_dec_ref_known(v___x_240_, 1);
v___x_242_ = l_Lean_FileMap_rangeContainsHoverPos(v_text_230_, v_val_241_, v_hoverPos_231_, v_includeStop_232_);
lean_dec(v_val_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec_ref(v_task_237_);
v___x_243_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_243_, 0, v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_233_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_task_pure(v___x_244_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_246_ = lean_box(v___x_242_);
v___f_247_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__0___boxed), 3, 2);
lean_closure_set(v___f_247_, 0, v___x_246_);
lean_closure_set(v___f_247_, 1, v___x_233_);
v___x_248_ = lean_unsigned_to_nat(0u);
v___x_249_ = lean_task_map(v___f_247_, v_task_237_, v___x_248_, v___x_242_);
return v___x_249_;
}
}
else
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
lean_dec(v___x_240_);
lean_dec_ref(v_task_237_);
v___x_250_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_233_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_task_pure(v___x_251_);
return v___x_252_;
}
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v_stx_x3f_236_);
lean_dec_ref(v_snap_234_);
v___x_253_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1));
v___x_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_233_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_task_pure(v___x_254_);
return v___x_255_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed(lean_object* v_text_256_, lean_object* v_hoverPos_257_, lean_object* v_includeStop_258_, lean_object* v___x_259_, lean_object* v_snap_260_, lean_object* v_x_261_){
_start:
{
uint8_t v_includeStop_boxed_262_; lean_object* v_res_263_; 
v_includeStop_boxed_262_ = lean_unbox(v_includeStop_258_);
v_res_263_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1(v_text_256_, v_hoverPos_257_, v_includeStop_boxed_262_, v___x_259_, v_snap_260_, v_x_261_);
lean_dec(v_x_261_);
lean_dec(v_hoverPos_257_);
lean_dec_ref(v_text_256_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos(lean_object* v_text_264_, lean_object* v_tree_265_, lean_object* v_hoverPos_266_, uint8_t v_includeStop_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___f_270_; lean_object* v___x_271_; 
v___x_268_ = lean_box(0);
v___x_269_ = lean_box(v_includeStop_267_);
v___f_270_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___boxed), 6, 4);
lean_closure_set(v___f_270_, 0, v_text_264_);
lean_closure_set(v___f_270_, 1, v_hoverPos_266_);
lean_closure_set(v___f_270_, 2, v___x_269_);
lean_closure_set(v___f_270_, 3, v___x_268_);
v___x_271_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_265_, v___x_268_, v___f_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_findInfoTreeAtPos___boxed(lean_object* v_text_272_, lean_object* v_tree_273_, lean_object* v_hoverPos_274_, lean_object* v_includeStop_275_){
_start:
{
uint8_t v_includeStop_boxed_276_; lean_object* v_res_277_; 
v_includeStop_boxed_276_ = lean_unbox(v_includeStop_275_);
v_res_277_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(v_text_272_, v_tree_273_, v_hoverPos_274_, v_includeStop_boxed_276_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(lean_object* v_requestedRange_278_, uint8_t v___x_279_, lean_object* v_f_280_, lean_object* v_ctx_281_, lean_object* v_i_282_, lean_object* v_acc_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_Elab_Info_range_x3f(v_i_282_);
if (lean_obj_tag(v___x_284_) == 1)
{
lean_object* v_val_285_; uint8_t v___x_286_; 
v_val_285_ = lean_ctor_get(v___x_284_, 0);
lean_inc(v_val_285_);
lean_dec_ref_known(v___x_284_, 1);
v___x_286_ = l_Lean_Syntax_Range_overlaps(v_val_285_, v_requestedRange_278_, v___x_279_, v___x_279_);
lean_dec(v_val_285_);
if (v___x_286_ == 0)
{
lean_dec_ref(v_i_282_);
lean_dec_ref(v_ctx_281_);
lean_dec(v_f_280_);
return v_acc_283_;
}
else
{
lean_object* v___x_287_; 
v___x_287_ = lean_apply_3(v_f_280_, v_ctx_281_, v_i_282_, v_acc_283_);
return v___x_287_;
}
}
else
{
lean_dec(v___x_284_);
lean_dec_ref(v_i_282_);
lean_dec_ref(v_ctx_281_);
lean_dec(v_f_280_);
return v_acc_283_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed(lean_object* v_requestedRange_288_, lean_object* v___x_289_, lean_object* v_f_290_, lean_object* v_ctx_291_, lean_object* v_i_292_, lean_object* v_acc_293_){
_start:
{
uint8_t v___x_559__boxed_294_; lean_object* v_res_295_; 
v___x_559__boxed_294_ = lean_unbox(v___x_289_);
v_res_295_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0(v_requestedRange_288_, v___x_559__boxed_294_, v_f_290_, v_ctx_291_, v_i_292_, v_acc_293_);
lean_dec_ref(v_requestedRange_288_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(lean_object* v___f_296_, lean_object* v_acc_297_, uint8_t v___x_298_, lean_object* v_tree_299_){
_start:
{
lean_object* v_element_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_315_; 
v_element_300_ = lean_ctor_get(v_tree_299_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v_tree_299_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; 
v_unused_316_ = lean_ctor_get(v_tree_299_, 1);
lean_dec(v_unused_316_);
v___x_302_ = v_tree_299_;
v_isShared_303_ = v_isSharedCheck_315_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_element_300_);
lean_dec(v_tree_299_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_315_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v_infoTree_x3f_304_; 
v_infoTree_x3f_304_ = lean_ctor_get(v_element_300_, 2);
lean_inc(v_infoTree_x3f_304_);
lean_dec_ref(v_element_300_);
if (lean_obj_tag(v_infoTree_x3f_304_) == 1)
{
lean_object* v_val_305_; lean_object* v_acc_306_; lean_object* v___x_307_; lean_object* v___x_309_; 
v_val_305_ = lean_ctor_get(v_infoTree_x3f_304_, 0);
lean_inc(v_val_305_);
lean_dec_ref_known(v_infoTree_x3f_304_, 1);
v_acc_306_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_296_, v_acc_297_, v_val_305_);
v___x_307_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_307_, 0, v___x_298_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_307_);
lean_ctor_set(v___x_302_, 0, v_acc_306_);
v___x_309_ = v___x_302_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_acc_306_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_307_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
else
{
lean_object* v___x_311_; lean_object* v___x_313_; 
lean_dec(v_infoTree_x3f_304_);
lean_dec(v___f_296_);
v___x_311_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_311_, 0, v___x_298_);
if (v_isShared_303_ == 0)
{
lean_ctor_set(v___x_302_, 1, v___x_311_);
lean_ctor_set(v___x_302_, 0, v_acc_297_);
v___x_313_ = v___x_302_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_acc_297_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_311_);
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
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed(lean_object* v___f_317_, lean_object* v_acc_318_, lean_object* v___x_319_, lean_object* v_tree_320_){
_start:
{
uint8_t v___x_571__boxed_321_; lean_object* v_res_322_; 
v___x_571__boxed_321_ = lean_unbox(v___x_319_);
v_res_322_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1(v___f_317_, v_acc_318_, v___x_571__boxed_321_, v_tree_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2(lean_object* v_requestedRange_323_, lean_object* v_f_324_, lean_object* v_snap_325_, lean_object* v_acc_326_){
_start:
{
lean_object* v_stx_x3f_327_; 
v_stx_x3f_327_ = lean_ctor_get(v_snap_325_, 0);
lean_inc(v_stx_x3f_327_);
if (lean_obj_tag(v_stx_x3f_327_) == 1)
{
lean_object* v_task_328_; lean_object* v_val_329_; uint8_t v___x_330_; lean_object* v___x_331_; 
v_task_328_ = lean_ctor_get(v_snap_325_, 3);
lean_inc_ref(v_task_328_);
lean_dec_ref(v_snap_325_);
v_val_329_ = lean_ctor_get(v_stx_x3f_327_, 0);
lean_inc(v_val_329_);
lean_dec_ref_known(v_stx_x3f_327_, 1);
v___x_330_ = 1;
v___x_331_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_329_, v___x_330_);
lean_dec(v_val_329_);
if (lean_obj_tag(v___x_331_) == 1)
{
lean_object* v_val_332_; uint8_t v___x_333_; 
v_val_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v___x_331_, 1);
v___x_333_ = l_Lean_Syntax_Range_overlaps(v_val_332_, v_requestedRange_323_, v___x_330_, v___x_330_);
lean_dec(v_val_332_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec_ref(v_task_328_);
lean_dec(v_f_324_);
lean_dec_ref(v_requestedRange_323_);
v___x_334_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_334_, 0, v___x_333_);
v___x_335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_335_, 0, v_acc_326_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_task_pure(v___x_335_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___f_338_; lean_object* v___x_339_; lean_object* v___f_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_337_ = lean_box(v___x_330_);
v___f_338_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_338_, 0, v_requestedRange_323_);
lean_closure_set(v___f_338_, 1, v___x_337_);
lean_closure_set(v___f_338_, 2, v_f_324_);
v___x_339_ = lean_box(v___x_330_);
v___f_340_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_340_, 0, v___f_338_);
lean_closure_set(v___f_340_, 1, v_acc_326_);
lean_closure_set(v___f_340_, 2, v___x_339_);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_task_map(v___f_340_, v_task_328_, v___x_341_, v___x_330_);
return v___x_342_;
}
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
lean_dec(v___x_331_);
lean_dec_ref(v_task_328_);
lean_dec(v_f_324_);
lean_dec_ref(v_requestedRange_323_);
v___x_343_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v_acc_326_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = lean_task_pure(v___x_344_);
return v___x_345_;
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec(v_stx_x3f_327_);
lean_dec_ref(v_snap_325_);
lean_dec(v_f_324_);
lean_dec_ref(v_requestedRange_323_);
v___x_346_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__1));
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v_acc_326_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_task_pure(v___x_347_);
return v___x_348_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(lean_object* v_tree_349_, lean_object* v_requestedRange_350_, lean_object* v_init_351_, lean_object* v_f_352_){
_start:
{
lean_object* v___f_353_; lean_object* v___x_354_; 
v___f_353_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_foldInfosInRange___redArg___lam__2), 4, 2);
lean_closure_set(v___f_353_, 0, v_requestedRange_350_);
lean_closure_set(v___f_353_, 1, v_f_352_);
v___x_354_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_349_, v_init_351_, v___f_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange(lean_object* v_00_u03b1_355_, lean_object* v_tree_356_, lean_object* v_requestedRange_357_, lean_object* v_init_358_, lean_object* v_f_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(v_tree_356_, v_requestedRange_357_, v_init_358_, v_f_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(lean_object* v_log_361_, uint8_t v___x_362_, lean_object* v_tree_363_){
_start:
{
lean_object* v_element_364_; lean_object* v_diagnostics_365_; lean_object* v_msgLog_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_375_; 
v_element_364_ = lean_ctor_get(v_tree_363_, 0);
lean_inc_ref(v_element_364_);
lean_dec_ref(v_tree_363_);
v_diagnostics_365_ = lean_ctor_get(v_element_364_, 1);
lean_inc_ref(v_diagnostics_365_);
lean_dec_ref(v_element_364_);
v_msgLog_366_ = lean_ctor_get(v_diagnostics_365_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v_diagnostics_365_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; 
v_unused_376_ = lean_ctor_get(v_diagnostics_365_, 1);
lean_dec(v_unused_376_);
v___x_368_ = v_diagnostics_365_;
v_isShared_369_ = v_isSharedCheck_375_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_msgLog_366_);
lean_dec(v_diagnostics_365_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_375_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_370_ = l_Lean_MessageLog_append(v_log_361_, v_msgLog_366_);
v___x_371_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_371_, 0, v___x_362_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v___x_371_);
lean_ctor_set(v___x_368_, 0, v___x_370_);
v___x_373_ = v___x_368_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_370_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed(lean_object* v_log_377_, lean_object* v___x_378_, lean_object* v_tree_379_){
_start:
{
uint8_t v___x_385__boxed_380_; lean_object* v_res_381_; 
v___x_385__boxed_380_ = lean_unbox(v___x_378_);
v_res_381_ = l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0(v_log_377_, v___x_385__boxed_380_, v_tree_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(lean_object* v_requestedRange_382_, lean_object* v_snap_383_, lean_object* v_log_384_){
_start:
{
lean_object* v_stx_x3f_385_; 
v_stx_x3f_385_ = lean_ctor_get(v_snap_383_, 0);
lean_inc(v_stx_x3f_385_);
if (lean_obj_tag(v_stx_x3f_385_) == 1)
{
lean_object* v_task_386_; lean_object* v_val_387_; uint8_t v___x_388_; lean_object* v___x_389_; 
v_task_386_ = lean_ctor_get(v_snap_383_, 3);
lean_inc_ref(v_task_386_);
lean_dec_ref(v_snap_383_);
v_val_387_ = lean_ctor_get(v_stx_x3f_385_, 0);
lean_inc(v_val_387_);
lean_dec_ref_known(v_stx_x3f_385_, 1);
v___x_388_ = 1;
v___x_389_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_val_387_, v___x_388_);
lean_dec(v_val_387_);
if (lean_obj_tag(v___x_389_) == 1)
{
lean_object* v_val_390_; uint8_t v___x_391_; 
v_val_390_ = lean_ctor_get(v___x_389_, 0);
lean_inc(v_val_390_);
lean_dec_ref_known(v___x_389_, 1);
v___x_391_ = l_Lean_Syntax_Range_overlaps(v_val_390_, v_requestedRange_382_, v___x_388_, v___x_388_);
lean_dec(v_val_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec_ref(v_task_386_);
v___x_392_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_392_, 0, v___x_391_);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v_log_384_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = lean_task_pure(v___x_393_);
return v___x_394_;
}
else
{
lean_object* v___x_395_; lean_object* v___f_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_395_ = lean_box(v___x_388_);
v___f_396_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__0___boxed), 3, 2);
lean_closure_set(v___f_396_, 0, v_log_384_);
lean_closure_set(v___f_396_, 1, v___x_395_);
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_task_map(v___f_396_, v_task_386_, v___x_397_, v___x_388_);
return v___x_398_;
}
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
lean_dec(v___x_389_);
lean_dec_ref(v_task_386_);
v___x_399_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_log_384_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = lean_task_pure(v___x_400_);
return v___x_401_;
}
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v_stx_x3f_385_);
lean_dec_ref(v_snap_383_);
v___x_402_ = ((lean_object*)(l_Lean_Language_SnapshotTree_findInfoTreeAtPos___lam__1___closed__0));
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v_log_384_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v___x_404_ = lean_task_pure(v___x_403_);
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed(lean_object* v_requestedRange_405_, lean_object* v_snap_406_, lean_object* v_log_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1(v_requestedRange_405_, v_snap_406_, v_log_407_);
lean_dec_ref(v_requestedRange_405_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange(lean_object* v_tree_409_, lean_object* v_requestedRange_410_){
_start:
{
lean_object* v___f_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___f_411_ = lean_alloc_closure((void*)(l_Lean_Language_SnapshotTree_collectMessagesInRange___lam__1___boxed), 3, 1);
lean_closure_set(v___f_411_, 0, v_requestedRange_410_);
v___x_412_ = l_Lean_MessageLog_empty;
v___x_413_ = l_Lean_Language_SnapshotTree_foldSnaps___redArg(v_tree_409_, v___x_412_, v___f_411_);
return v___x_413_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos(lean_object* v_hoverPos_414_, lean_object* v_cmdParsed_415_){
_start:
{
lean_object* v_stx_416_; uint8_t v___x_417_; lean_object* v___x_418_; 
v_stx_416_ = lean_ctor_get(v_cmdParsed_415_, 1);
v___x_417_ = 1;
v___x_418_ = l_Lean_Syntax_getPos_x3f(v_stx_416_, v___x_417_);
if (lean_obj_tag(v___x_418_) == 1)
{
lean_object* v_val_419_; lean_object* v___x_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_val_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_val_419_);
lean_dec_ref_known(v___x_418_, 1);
v___x_420_ = lean_unsigned_to_nat(1u);
v___x_421_ = lean_nat_add(v_hoverPos_414_, v___x_420_);
v___x_422_ = lean_nat_dec_le(v___x_421_, v_val_419_);
lean_dec(v_val_419_);
lean_dec(v___x_421_);
return v___x_422_;
}
else
{
uint8_t v___x_423_; 
lean_dec(v___x_418_);
v___x_423_ = 0;
return v___x_423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos___boxed(lean_object* v_hoverPos_424_, lean_object* v_cmdParsed_425_){
_start:
{
uint8_t v_res_426_; lean_object* v_r_427_; 
v_res_426_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos(v_hoverPos_424_, v_cmdParsed_425_);
lean_dec_ref(v_cmdParsed_425_);
lean_dec(v_hoverPos_424_);
v_r_427_ = lean_box(v_res_426_);
return v_r_427_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos(lean_object* v_text_428_, lean_object* v_hoverPos_429_, lean_object* v_cmdParsed_430_){
_start:
{
lean_object* v_stx_431_; uint8_t v___x_432_; lean_object* v___x_433_; 
v_stx_431_ = lean_ctor_get(v_cmdParsed_430_, 1);
v___x_432_ = 1;
v___x_433_ = l_Lean_Syntax_getRangeWithTrailing_x3f(v_stx_431_, v___x_432_);
if (lean_obj_tag(v___x_433_) == 1)
{
lean_object* v_val_434_; uint8_t v___x_435_; uint8_t v___x_436_; 
v_val_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_val_434_);
lean_dec_ref_known(v___x_433_, 1);
v___x_435_ = 0;
v___x_436_ = l_Lean_FileMap_rangeContainsHoverPos(v_text_428_, v_val_434_, v_hoverPos_429_, v___x_435_);
lean_dec(v_val_434_);
return v___x_436_;
}
else
{
uint8_t v___x_437_; 
lean_dec(v___x_433_);
v___x_437_ = 0;
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos___boxed(lean_object* v_text_438_, lean_object* v_hoverPos_439_, lean_object* v_cmdParsed_440_){
_start:
{
uint8_t v_res_441_; lean_object* v_r_442_; 
v_res_441_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos(v_text_438_, v_hoverPos_439_, v_cmdParsed_440_);
lean_dec_ref(v_cmdParsed_440_);
lean_dec(v_hoverPos_439_);
lean_dec_ref(v_text_438_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
static lean_object* _init_l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0(void){
_start:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_box(0);
v___x_444_ = lean_task_pure(v___x_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go(lean_object* v_text_445_, lean_object* v_hoverPos_446_, lean_object* v_cmdParsed_447_){
_start:
{
uint8_t v___x_448_; 
v___x_448_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_containsHoverPos(v_text_445_, v_hoverPos_446_, v_cmdParsed_447_);
if (v___x_448_ == 0)
{
uint8_t v___x_449_; 
v___x_449_ = l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_isAfterHoverPos(v_hoverPos_446_, v_cmdParsed_447_);
if (v___x_449_ == 0)
{
lean_object* v_nextCmdSnap_x3f_450_; 
v_nextCmdSnap_x3f_450_ = lean_ctor_get(v_cmdParsed_447_, 4);
lean_inc(v_nextCmdSnap_x3f_450_);
lean_dec_ref(v_cmdParsed_447_);
if (lean_obj_tag(v_nextCmdSnap_x3f_450_) == 0)
{
lean_object* v___x_451_; 
lean_dec(v_hoverPos_446_);
lean_dec_ref(v_text_445_);
v___x_451_ = lean_obj_once(&l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0, &l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0);
return v___x_451_;
}
else
{
lean_object* v_val_452_; lean_object* v_task_453_; uint8_t v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v_val_452_ = lean_ctor_get(v_nextCmdSnap_x3f_450_, 0);
lean_inc(v_val_452_);
lean_dec_ref_known(v_nextCmdSnap_x3f_450_, 1);
v_task_453_ = lean_ctor_get(v_val_452_, 3);
lean_inc_ref(v_task_453_);
lean_dec(v_val_452_);
v___x_454_ = 1;
v___x_455_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go), 3, 2);
lean_closure_set(v___x_455_, 0, v_text_445_);
lean_closure_set(v___x_455_, 1, v_hoverPos_446_);
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_task_bind(v_task_453_, v___x_455_, v___x_456_, v___x_454_);
return v___x_457_;
}
}
else
{
lean_object* v___x_458_; 
lean_dec_ref(v_cmdParsed_447_);
lean_dec(v_hoverPos_446_);
lean_dec_ref(v_text_445_);
v___x_458_ = lean_obj_once(&l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0, &l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0);
return v___x_458_;
}
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec(v_hoverPos_446_);
lean_dec_ref(v_text_445_);
v___x_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_459_, 0, v_cmdParsed_447_);
v___x_460_ = lean_task_pure(v___x_459_);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdParsedSnap___lam__0(lean_object* v_text_461_, lean_object* v_hoverPos_462_, lean_object* v_headerProcessed_463_){
_start:
{
lean_object* v_result_x3f_464_; 
v_result_x3f_464_ = lean_ctor_get(v_headerProcessed_463_, 2);
lean_inc(v_result_x3f_464_);
lean_dec_ref(v_headerProcessed_463_);
if (lean_obj_tag(v_result_x3f_464_) == 1)
{
lean_object* v_val_465_; lean_object* v_firstCmdSnap_466_; lean_object* v_task_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; lean_object* v___x_471_; 
v_val_465_ = lean_ctor_get(v_result_x3f_464_, 0);
lean_inc(v_val_465_);
lean_dec_ref_known(v_result_x3f_464_, 1);
v_firstCmdSnap_466_ = lean_ctor_get(v_val_465_, 1);
lean_inc_ref(v_firstCmdSnap_466_);
lean_dec(v_val_465_);
v_task_467_ = lean_ctor_get(v_firstCmdSnap_466_, 3);
lean_inc_ref(v_task_467_);
lean_dec_ref(v_firstCmdSnap_466_);
v___x_468_ = lean_alloc_closure((void*)(l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go), 3, 2);
lean_closure_set(v___x_468_, 0, v_text_461_);
lean_closure_set(v___x_468_, 1, v_hoverPos_462_);
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = 1;
v___x_471_ = lean_task_bind(v_task_467_, v___x_468_, v___x_469_, v___x_470_);
return v___x_471_;
}
else
{
lean_object* v___x_472_; 
lean_dec(v_result_x3f_464_);
lean_dec(v_hoverPos_462_);
lean_dec_ref(v_text_461_);
v___x_472_ = lean_obj_once(&l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0, &l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdParsedSnap(lean_object* v_initSnap_473_, lean_object* v_text_474_, lean_object* v_hoverPos_475_){
_start:
{
lean_object* v_result_x3f_476_; 
v_result_x3f_476_ = lean_ctor_get(v_initSnap_473_, 4);
lean_inc(v_result_x3f_476_);
lean_dec_ref(v_initSnap_473_);
if (lean_obj_tag(v_result_x3f_476_) == 1)
{
lean_object* v_val_477_; lean_object* v_processedSnap_478_; lean_object* v_task_479_; lean_object* v___f_480_; lean_object* v___x_481_; uint8_t v___x_482_; lean_object* v___x_483_; 
v_val_477_ = lean_ctor_get(v_result_x3f_476_, 0);
lean_inc(v_val_477_);
lean_dec_ref_known(v_result_x3f_476_, 1);
v_processedSnap_478_ = lean_ctor_get(v_val_477_, 1);
lean_inc_ref(v_processedSnap_478_);
lean_dec(v_val_477_);
v_task_479_ = lean_ctor_get(v_processedSnap_478_, 3);
lean_inc_ref(v_task_479_);
lean_dec_ref(v_processedSnap_478_);
v___f_480_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_findCmdParsedSnap___lam__0), 3, 2);
lean_closure_set(v___f_480_, 0, v_text_474_);
lean_closure_set(v___f_480_, 1, v_hoverPos_475_);
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = 1;
v___x_483_ = lean_task_bind(v_task_479_, v___f_480_, v___x_481_, v___x_482_);
return v___x_483_;
}
else
{
lean_object* v___x_484_; 
lean_dec(v_result_x3f_476_);
lean_dec(v_hoverPos_475_);
lean_dec_ref(v_text_474_);
v___x_484_ = lean_obj_once(&l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0, &l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0_once, _init_l___private_Lean_Language_Lean_Util_0__Lean_Language_Lean_findCmdParsedSnap_go___closed__0);
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Language_Lean_findCmdDataAtPos_spec__0(lean_object* v_msg_485_){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_box(0);
v___x_487_ = lean_panic_fn_borrowed(v___x_486_, v_msg_485_);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_491_ = ((lean_object*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__2));
v___x_492_ = lean_unsigned_to_nat(8u);
v___x_493_ = lean_unsigned_to_nat(199u);
v___x_494_ = ((lean_object*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__1));
v___x_495_ = ((lean_object*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__0));
v___x_496_ = l_mkPanicMessageWithDecl(v___x_495_, v___x_494_, v___x_493_, v___x_492_, v___x_491_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__0(lean_object* v_stx_497_, lean_object* v_s_498_){
_start:
{
lean_object* v_infoTree_x3f_499_; 
v_infoTree_x3f_499_ = lean_ctor_get(v_s_498_, 2);
lean_inc(v_infoTree_x3f_499_);
lean_dec_ref(v_s_498_);
if (lean_obj_tag(v_infoTree_x3f_499_) == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec(v_stx_497_);
v___x_500_ = lean_obj_once(&l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3, &l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3_once, _init_l_Lean_Language_Lean_findCmdDataAtPos___lam__0___closed__3);
v___x_501_ = l_panic___at___00Lean_Language_Lean_findCmdDataAtPos_spec__0(v___x_500_);
return v___x_501_;
}
else
{
lean_object* v_val_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_510_; 
v_val_502_ = lean_ctor_get(v_infoTree_x3f_499_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_infoTree_x3f_499_);
if (v_isSharedCheck_510_ == 0)
{
v___x_504_ = v_infoTree_x3f_499_;
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_val_502_);
lean_dec(v_infoTree_x3f_499_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_510_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v_stx_497_);
lean_ctor_set(v___x_506_, 1, v_val_502_);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_506_);
v___x_508_ = v___x_504_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__1(lean_object* v_elabSnap_511_, lean_object* v___f_512_, lean_object* v_stx_513_, lean_object* v_x_514_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
lean_object* v_infoTreeSnap_515_; lean_object* v_task_516_; lean_object* v___x_517_; uint8_t v___x_518_; lean_object* v___x_519_; 
lean_dec(v_stx_513_);
v_infoTreeSnap_515_ = lean_ctor_get(v_elabSnap_511_, 3);
lean_inc_ref(v_infoTreeSnap_515_);
lean_dec_ref(v_elabSnap_511_);
v_task_516_ = lean_ctor_get(v_infoTreeSnap_515_, 3);
lean_inc_ref(v_task_516_);
lean_dec_ref(v_infoTreeSnap_515_);
v___x_517_ = lean_unsigned_to_nat(0u);
v___x_518_ = 1;
v___x_519_ = lean_task_map(v___f_512_, v_task_516_, v___x_517_, v___x_518_);
return v___x_519_;
}
else
{
lean_object* v_val_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_529_; 
lean_dec_ref(v___f_512_);
lean_dec_ref(v_elabSnap_511_);
v_val_520_ = lean_ctor_get(v_x_514_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v_x_514_);
if (v_isSharedCheck_529_ == 0)
{
v___x_522_ = v_x_514_;
v_isShared_523_ = v_isSharedCheck_529_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_val_520_);
lean_dec(v_x_514_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_529_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_524_, 0, v_stx_513_);
lean_ctor_set(v___x_524_, 1, v_val_520_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_524_);
v___x_526_ = v___x_522_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_528_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_527_; 
v___x_527_ = lean_task_pure(v___x_526_);
return v___x_527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0(lean_object* v_s_532_, lean_object* v___y_533_){
_start:
{
lean_object* v_toSnapshot_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_toSnapshot_534_ = lean_ctor_get(v_s_532_, 0);
lean_inc_ref(v_toSnapshot_534_);
lean_dec_ref(v_s_532_);
v___x_535_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_534_, v___y_533_);
v___x_536_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0));
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_535_);
lean_ctor_set(v___x_537_, 1, v___x_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___boxed(lean_object* v_s_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0(v_s_538_, v___y_539_);
lean_dec_ref(v___y_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2(lean_object* v_t_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___f_544_; lean_object* v___x_545_; 
v___f_544_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___closed__0));
v___x_545_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_542_, v___f_544_, v_a_543_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___boxed(lean_object* v_t_546_, lean_object* v_a_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2(v_t_546_, v_a_547_);
lean_dec_ref(v_a_547_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4(lean_object* v_t_550_, lean_object* v_a_551_){
_start:
{
lean_object* v___f_552_; lean_object* v___x_553_; 
v___f_552_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___closed__0));
v___x_553_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_550_, v___f_552_, v_a_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4___boxed(lean_object* v_t_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4(v_t_554_, v_a_555_);
lean_dec_ref(v_a_555_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0(lean_object* v_s_557_, lean_object* v___y_558_){
_start:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = l_Lean_Language_Snapshot_transform(v_s_557_, v___y_558_);
v___x_560_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2___lam__0___closed__0));
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0___boxed(lean_object* v_s_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___lam__0(v_s_562_, v___y_563_);
lean_dec_ref(v___y_563_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3(lean_object* v_t_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___f_568_; lean_object* v___x_569_; 
v___f_568_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___closed__0));
v___x_569_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_566_, v___f_568_, v_a_567_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3___boxed(lean_object* v_t_570_, lean_object* v_a_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3(v_t_570_, v_a_571_);
lean_dec_ref(v_a_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0(lean_object* v_s_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_toSnapshotTreeM_575_; lean_object* v___x_576_; 
v_toSnapshotTreeM_575_ = lean_ctor_get(v_s_573_, 1);
lean_inc_ref(v_toSnapshotTreeM_575_);
lean_dec_ref(v_s_573_);
lean_inc_ref(v___y_574_);
v___x_576_ = lean_apply_1(v_toSnapshotTreeM_575_, v___y_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0___boxed(lean_object* v_s_577_, lean_object* v___y_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___lam__0(v_s_577_, v___y_578_);
lean_dec_ref(v___y_578_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1(lean_object* v_t_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___f_583_; lean_object* v___x_584_; 
v___f_583_ = ((lean_object*)(l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___closed__0));
v___x_584_ = l_Lean_Language_SnapshotTask_transformWith___redArg(v_t_581_, v___f_583_, v_a_582_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1___boxed(lean_object* v_t_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1(v_t_585_, v_a_586_);
lean_dec_ref(v_a_586_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1(lean_object* v_a_588_){
_start:
{
lean_object* v_toSnapshot_589_; lean_object* v_elabSnap_590_; lean_object* v_resultSnap_591_; lean_object* v_infoTreeSnap_592_; lean_object* v_reportSnap_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_toSnapshot_589_ = lean_ctor_get(v_a_588_, 0);
lean_inc_ref(v_toSnapshot_589_);
v_elabSnap_590_ = lean_ctor_get(v_a_588_, 1);
lean_inc_ref(v_elabSnap_590_);
v_resultSnap_591_ = lean_ctor_get(v_a_588_, 2);
lean_inc_ref(v_resultSnap_591_);
v_infoTreeSnap_592_ = lean_ctor_get(v_a_588_, 3);
lean_inc_ref(v_infoTreeSnap_592_);
v_reportSnap_593_ = lean_ctor_get(v_a_588_, 4);
lean_inc_ref(v_reportSnap_593_);
lean_dec_ref(v_a_588_);
v___x_594_ = l_Lean_Language_instInhabitedSnapshotTreeTransform_default;
v___x_595_ = l_Lean_Language_Snapshot_transform(v_toSnapshot_589_, v___x_594_);
v___x_596_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__1(v_elabSnap_590_, v___x_594_);
v___x_597_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__2(v_resultSnap_591_, v___x_594_);
v___x_598_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__3(v_infoTreeSnap_592_, v___x_594_);
v___x_599_ = l_Lean_Language_SnapshotTask_transform___at___00Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1_spec__4(v_reportSnap_593_, v___x_594_);
v___x_600_ = lean_unsigned_to_nat(4u);
v___x_601_ = lean_mk_empty_array_with_capacity(v___x_600_);
v___x_602_ = lean_array_push(v___x_601_, v___x_596_);
v___x_603_ = lean_array_push(v___x_602_, v___x_597_);
v___x_604_ = lean_array_push(v___x_603_, v___x_598_);
v___x_605_ = lean_array_push(v___x_604_, v___x_599_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_595_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
return v___x_606_;
}
}
static lean_object* _init_l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0(void){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_607_ = lean_box(0);
v___x_608_ = lean_task_pure(v___x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__2(lean_object* v_text_609_, lean_object* v_hoverPos_610_, uint8_t v_includeStop_611_, lean_object* v_x_612_){
_start:
{
if (lean_obj_tag(v_x_612_) == 0)
{
lean_object* v___x_613_; 
lean_dec(v_hoverPos_610_);
lean_dec_ref(v_text_609_);
v___x_613_ = lean_obj_once(&l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0, &l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0_once, _init_l_Lean_Language_Lean_findCmdDataAtPos___lam__2___closed__0);
return v___x_613_;
}
else
{
lean_object* v_val_614_; lean_object* v_stx_615_; lean_object* v_elabSnap_616_; lean_object* v___f_617_; lean_object* v___f_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; lean_object* v___x_623_; 
v_val_614_ = lean_ctor_get(v_x_612_, 0);
lean_inc(v_val_614_);
lean_dec_ref_known(v_x_612_, 1);
v_stx_615_ = lean_ctor_get(v_val_614_, 1);
lean_inc_n(v_stx_615_, 2);
v_elabSnap_616_ = lean_ctor_get(v_val_614_, 3);
lean_inc_ref_n(v_elabSnap_616_, 2);
lean_dec(v_val_614_);
v___f_617_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__0), 2, 1);
lean_closure_set(v___f_617_, 0, v_stx_615_);
v___f_618_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__1), 4, 3);
lean_closure_set(v___f_618_, 0, v_elabSnap_616_);
lean_closure_set(v___f_618_, 1, v___f_617_);
lean_closure_set(v___f_618_, 2, v_stx_615_);
v___x_619_ = l_Lean_Language_toSnapshotTree___at___00Lean_Language_Lean_findCmdDataAtPos_spec__1(v_elabSnap_616_);
v___x_620_ = l_Lean_Language_SnapshotTree_findInfoTreeAtPos(v_text_609_, v___x_619_, v_hoverPos_610_, v_includeStop_611_);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = 1;
v___x_623_ = lean_task_bind(v___x_620_, v___f_618_, v___x_621_, v___x_622_);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___lam__2___boxed(lean_object* v_text_624_, lean_object* v_hoverPos_625_, lean_object* v_includeStop_626_, lean_object* v_x_627_){
_start:
{
uint8_t v_includeStop_boxed_628_; lean_object* v_res_629_; 
v_includeStop_boxed_628_ = lean_unbox(v_includeStop_626_);
v_res_629_ = l_Lean_Language_Lean_findCmdDataAtPos___lam__2(v_text_624_, v_hoverPos_625_, v_includeStop_boxed_628_, v_x_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos(lean_object* v_initSnap_630_, lean_object* v_text_631_, lean_object* v_hoverPos_632_, uint8_t v_includeStop_633_){
_start:
{
lean_object* v___x_634_; lean_object* v___f_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; lean_object* v___x_639_; 
v___x_634_ = lean_box(v_includeStop_633_);
lean_inc(v_hoverPos_632_);
lean_inc_ref(v_text_631_);
v___f_635_ = lean_alloc_closure((void*)(l_Lean_Language_Lean_findCmdDataAtPos___lam__2___boxed), 4, 3);
lean_closure_set(v___f_635_, 0, v_text_631_);
lean_closure_set(v___f_635_, 1, v_hoverPos_632_);
lean_closure_set(v___f_635_, 2, v___x_634_);
v___x_636_ = l_Lean_Language_Lean_findCmdParsedSnap(v_initSnap_630_, v_text_631_, v_hoverPos_632_);
v___x_637_ = lean_unsigned_to_nat(0u);
v___x_638_ = 1;
v___x_639_ = lean_task_bind(v___x_636_, v___f_635_, v___x_637_, v___x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findCmdDataAtPos___boxed(lean_object* v_initSnap_640_, lean_object* v_text_641_, lean_object* v_hoverPos_642_, lean_object* v_includeStop_643_){
_start:
{
uint8_t v_includeStop_boxed_644_; lean_object* v_res_645_; 
v_includeStop_boxed_644_ = lean_unbox(v_includeStop_643_);
v_res_645_ = l_Lean_Language_Lean_findCmdDataAtPos(v_initSnap_640_, v_text_641_, v_hoverPos_642_, v_includeStop_boxed_644_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos___lam__0(lean_object* v_x_646_){
_start:
{
if (lean_obj_tag(v_x_646_) == 0)
{
lean_object* v___x_647_; 
v___x_647_ = lean_box(0);
return v___x_647_;
}
else
{
lean_object* v_val_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_656_; 
v_val_648_ = lean_ctor_get(v_x_646_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v_x_646_);
if (v_isSharedCheck_656_ == 0)
{
v___x_650_ = v_x_646_;
v_isShared_651_ = v_isSharedCheck_656_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_val_648_);
lean_dec(v_x_646_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_656_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v_snd_652_; lean_object* v___x_654_; 
v_snd_652_ = lean_ctor_get(v_val_648_, 1);
lean_inc(v_snd_652_);
lean_dec(v_val_648_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v_snd_652_);
v___x_654_ = v___x_650_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v_snd_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos(lean_object* v_initSnap_658_, lean_object* v_text_659_, lean_object* v_hoverPos_660_, uint8_t v_includeStop_661_){
_start:
{
lean_object* v___f_662_; lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___x_666_; 
v___f_662_ = ((lean_object*)(l_Lean_Language_Lean_findInfoTreeAtPos___closed__0));
v___x_663_ = l_Lean_Language_Lean_findCmdDataAtPos(v_initSnap_658_, v_text_659_, v_hoverPos_660_, v_includeStop_661_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = 1;
v___x_666_ = lean_task_map(v___f_662_, v___x_663_, v___x_664_, v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Language_Lean_findInfoTreeAtPos___boxed(lean_object* v_initSnap_667_, lean_object* v_text_668_, lean_object* v_hoverPos_669_, lean_object* v_includeStop_670_){
_start:
{
uint8_t v_includeStop_boxed_671_; lean_object* v_res_672_; 
v_includeStop_boxed_671_ = lean_unbox(v_includeStop_670_);
v_res_672_ = l_Lean_Language_Lean_findInfoTreeAtPos(v_initSnap_667_, v_text_668_, v_hoverPos_669_, v_includeStop_boxed_671_);
return v_res_672_;
}
}
lean_object* runtime_initialize_Lean_Language_Lean_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Language_Lean_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Language_Lean_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Language_Lean_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Language_Lean_Types(uint8_t builtin);
lean_object* initialize_Lean_Elab_InfoTree_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Language_Lean_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Language_Lean_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Language_Lean_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Language_Lean_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Language_Lean_Util(builtin);
}
#ifdef __cplusplus
}
#endif
