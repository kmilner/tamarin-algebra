#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

/* Two classes of Lean export are wrapped here (lean/ExportManifest.txt). The reply of a contract
 * export is specified by theorems and may be used as the answer: total_unify, unpack_conjunction,
 * total_unify_exists, total_match, total_match_exists, certify_table, session_reduce,
 * path_reduce, session_variant_check and the theory_* exports over the theory of a Tamarin file.
 * Every other export, checked_variants, general_variants and
 * fold_variants included, is a proposer with no contract: its output may only go into a
 * proposed family of variants that tamarin_lean_session_variant_check then has to accept. */

/* The generated module initializer and export use the pinned Lean ABI. */
extern lean_object *initialize_tamarin_x2dspec_TamarinRuntime(uint8_t builtin);
extern uint8_t tamarin_flat_ac_equal(lean_object *lhs, lean_object *rhs);
extern lean_object *tamarin_flat_ac_residual(lean_object *tail, lean_object *rhs);
extern void lean_initialize_thread(void);
extern void lean_finalize_thread(void);

/* Serialized exactly once by Rust's OnceLock, before any worker calls Lean. */
uint8_t tamarin_lean_initialize(void) {
    lean_object *result = initialize_tamarin_x2dspec_TamarinRuntime(1);
    if (!lean_io_result_is_ok(result)) {
        lean_dec(result);
        return 1;
    }
    lean_dec(result);
    lean_io_mark_end_initialization();
    return 0;
}

void tamarin_lean_thread_initialize(void) { lean_initialize_thread(); }
void tamarin_lean_thread_finalize(void) { lean_finalize_thread(); }

static lean_object *atom_array(const uint64_t *atoms, size_t length) {
    lean_object *array = lean_alloc_array(length, length);
    for (size_t i = 0; i < length; ++i) {
        lean_array_set_core(array, i, lean_box_uint64(atoms[i]));
    }
    return array;
}

extern lean_object *tamarin_operand_refine(lean_object *sides);

size_t tamarin_lean_operand_refine(const uint64_t *sides, size_t count, uint64_t *indices) {
    lean_object *result = tamarin_operand_refine(atom_array(sides, count));
    size_t n = lean_array_size(result);
    if (n <= count / 2) {
        for (size_t i = 0; i < n; ++i)
            indices[i] = lean_unbox_uint64(lean_array_get_core(result, i));
    } else {
        n = SIZE_MAX;
    }
    lean_dec(result);
    return n;
}

extern uint8_t tamarin_residual_rigid(uint8_t lk, uint64_t lh, lean_object *ls,
                                     uint8_t rk, uint64_t rh, lean_object *rs);

uint8_t tamarin_lean_residual_rigid(uint8_t lk, uint64_t lh, const uint64_t *ls, size_t nl,
                                    uint8_t rk, uint64_t rh, const uint64_t *rs, size_t nr) {
    return tamarin_residual_rigid(lk, lh, atom_array(ls, nl), rk, rh, atom_array(rs, nr));
}

extern uint8_t tamarin_residual_variable(uint8_t right, uint64_t key, uint64_t key_sort,
                                         uint8_t kind, uint64_t value_sort, lean_object *ids);

uint8_t tamarin_lean_residual_variable(uint8_t right, uint64_t key, uint64_t key_sort, uint8_t kind,
                                      uint64_t value_sort, const uint64_t *ids, size_t count) {
    return tamarin_residual_variable(right, key, key_sort, kind, value_sort, atom_array(ids, count));
}

extern lean_object *tamarin_cancel_common(lean_object *left, lean_object *right);
uint8_t tamarin_lean_cancel_common(const uint64_t *left, size_t left_size,
                                   const uint64_t *right, size_t right_size,
                                   uint64_t *left_out, size_t *left_len,
                                   uint64_t *right_out, size_t *right_len) {
    lean_object *result = tamarin_cancel_common(atom_array(left, left_size), atom_array(right, right_size));
    if (lean_array_size(result) != 2) {
        lean_dec(result);
        return 255;
    }
    lean_object *l = lean_array_get_core(result, 0);
    lean_object *r = lean_array_get_core(result, 1);
    *left_len = lean_array_size(l);
    *right_len = lean_array_size(r);
    if (*left_len > left_size || *right_len > right_size) {
        lean_dec(result);
        return 255;
    }
    for (size_t i = 0; i < *left_len; i++)
        left_out[i] = lean_unbox_uint64(lean_array_get_core(l, i));
    for (size_t i = 0; i < *right_len; i++)
        right_out[i] = lean_unbox_uint64(lean_array_get_core(r, i));
    lean_dec(result);
    return 0;
}

extern uint8_t tamarin_constructor_variant(lean_object *roots, lean_object *used);
extern uint8_t tamarin_ground_variant(lean_object *holes, lean_object *anchors,
                                      lean_object *deps, uint8_t rigid);
uint8_t tamarin_lean_ground_variant(const uint64_t *holes, size_t hole_count,
                                    const uint64_t *anchors, size_t anchor_count,
                                    const uint64_t *deps, size_t dep_count, uint8_t rigid) {
    return tamarin_ground_variant(atom_array(holes, hole_count), atom_array(anchors, anchor_count),
                                  atom_array(deps, dep_count), rigid);
}

extern uint8_t tamarin_exclude_root(lean_object *rows, lean_object *args);

uint8_t tamarin_lean_exclude_root(const uint64_t *words, size_t row_count,
                                  const uint64_t *args, size_t arity) {
    lean_object *rows = lean_alloc_array(row_count, row_count);
    for (size_t i = 0; i < row_count; ++i)
        lean_array_set_core(rows, i, atom_array(words + i * arity, arity));
    return tamarin_exclude_root(rows, atom_array(args, arity));
}

uint8_t tamarin_lean_constructor_variant(const uint64_t *roots, size_t root_count,
                                        const uint64_t *used, size_t used_count) {
    return tamarin_constructor_variant(atom_array(roots, root_count), atom_array(used, used_count));
}

extern lean_object *tamarin_reduce_rule_slot(uint64_t slot, lean_object *keys, lean_object *subjects);
uint8_t tamarin_lean_reduce_rule_slot(uint64_t slot, const uint64_t *keys,
                                     const uint64_t *subjects, size_t length, uint64_t *out) {
    lean_object *result = tamarin_reduce_rule_slot(slot, atom_array(keys, length),
                                                 atom_array(subjects, length));
    size_t count = lean_array_size(result);
    if (count == 1) *out = lean_unbox_uint64(lean_array_get_core(result, 0));
    lean_dec(result);
    return count > 1 ? 255 : (uint8_t)count;
}

/* The exported Lean function consumes both arrays. No Lean object or owned
 * allocation crosses back into Rust. The input slices remain Rust-owned. */
uint8_t tamarin_lean_flat_ac_equal(const uint64_t *lhs, size_t lhs_length,
                                 const uint64_t *rhs, size_t rhs_length) {
    return tamarin_flat_ac_equal(atom_array(lhs, lhs_length),
                                atom_array(rhs, rhs_length));
}

/* Output is [status, residual atoms...] in Lean. Copy into the caller's
 * buffer and release the array here, keeping allocation ownership local. */
uint8_t tamarin_lean_flat_ac_residual(const uint64_t *tail, size_t tail_length,
                                    const uint64_t *rhs, size_t rhs_length,
                                    uint64_t *residual, size_t capacity,
                                    size_t *residual_length) {
    *residual_length = 0;
    lean_object *result = tamarin_flat_ac_residual(atom_array(tail, tail_length),
                                                 atom_array(rhs, rhs_length));
    size_t length = lean_array_size(result);
    if (length == 0) {
        lean_dec(result);
        return 255;
    }
    uint64_t status = lean_unbox_uint64(lean_array_get_core(result, 0));
    size_t count = length - 1;
    if (status > 2 || count > capacity || (status == 2 && count == 0) ||
        (status != 2 && count != 0)) {
        lean_dec(result);
        return 255;
    }
    for (size_t i = 0; i < count; ++i) {
        residual[i] = lean_unbox_uint64(lean_array_get_core(result, i + 1));
    }
    *residual_length = count;
    lean_dec(result);
    return (uint8_t)status;
}

extern uint8_t tamarin_collector_possible(lean_object *occ, lean_object *residual);

uint8_t tamarin_lean_collector_possible(const uint64_t *occ, size_t occurrence_count,
                                        const uint64_t *residual, size_t residual_count) {
    return tamarin_collector_possible(atom_array(occ, occurrence_count),
                                      atom_array(residual, residual_count));
}

/* Nested numeric rows avoid textual serialization and variable-name parsing.
 * The Rust guard owns this opaque result until every requested row is copied. */
extern lean_object *tamarin_flat_ac_match(uint64_t n, lean_object *occ,
                                        lean_object *tail, lean_object *rhs);
void *tamarin_lean_flat_ac_match(uint64_t n,
                               const uint64_t *occ, size_t occ_length,
                               const uint64_t *tail, size_t tail_length,
                               const uint64_t *rhs, size_t rhs_length) {
    return tamarin_flat_ac_match(n, atom_array(occ, occ_length),
                                atom_array(tail, tail_length), atom_array(rhs, rhs_length));
}
size_t tamarin_lean_match_count(const void *result) {
    return lean_array_size((lean_object *)result);
}
size_t tamarin_lean_match_rows(const void *result, size_t answer) {
    lean_object *answers = (lean_object *)result;
    if (answer >= lean_array_size(answers)) return SIZE_MAX;
    return lean_array_size(lean_array_get_core(answers, answer));
}
uint8_t tamarin_lean_match_row(const void *result, size_t answer, size_t variable,
                             uint64_t *out, size_t capacity, size_t *length) {
    *length = 0;
    lean_object *answers = (lean_object *)result;
    if (answer >= lean_array_size(answers)) return 255;
    lean_object *rows = lean_array_get_core(answers, answer);
    if (variable >= lean_array_size(rows)) return 255;
    lean_object *row = lean_array_get_core(rows, variable);
    size_t size = lean_array_size(row);
    if (size == 0 || size > capacity) return 255;
    for (size_t i = 0; i < size; ++i)
        out[i] = lean_unbox_uint64(lean_array_get_core(row, i));
    *length = size;
    return 0;
}
void tamarin_lean_match_release(void *result) { lean_dec((lean_object *)result); }

typedef struct {
    const uint64_t *data;
    size_t size;
} whole_word_slice;

extern uint8_t tamarin_check_factors(lean_object *, lean_object *, lean_object *,
                                     lean_object *, lean_object *);

static lean_object *word_rows(const whole_word_slice *rows, size_t count) {
    lean_object *nodes = lean_alloc_array(count, count);
    for (size_t i = 0; i < count; ++i)
        lean_array_set_core(nodes, i, atom_array(rows[i].data, rows[i].size));
    return nodes;
}

extern uint8_t tamarin_ac_bag_match(lean_object *rows);
uint8_t tamarin_lean_ac_bag_match(const whole_word_slice *rows, size_t count) {
    return tamarin_ac_bag_match(word_rows(rows, count));
}

extern uint8_t tamarin_ac_bag_typed_match(lean_object *rows, lean_object *restrictions);
uint8_t tamarin_lean_ac_bag_typed_match(const whole_word_slice *rows, size_t count,
                                       const whole_word_slice *restrictions, size_t restricted) {
    return tamarin_ac_bag_typed_match(word_rows(rows, count),
                                     word_rows(restrictions, restricted));
}

extern lean_object *tamarin_select_joined_variants(lean_object *rows);
uint8_t tamarin_lean_select_joined_variants(const whole_word_slice *rows, size_t count,
                                           uint8_t *mask) {
    lean_object *reply = tamarin_select_joined_variants(word_rows(rows, count));
    if (lean_is_scalar(reply)) return 0;
    lean_object *flags = lean_ctor_get(reply, 0);
    uint8_t status = 255;
    if (lean_array_size(flags) == count) {
        status = 1;
        for (size_t i = 0; i < count; ++i) {
            uint64_t flag = lean_unbox_uint64(lean_array_get_core(flags, i));
            if (flag > 1) { status = 255; break; }
            mask[i] = (uint8_t)flag;
        }
    }
    lean_dec(reply);
    return status;
}

extern uint8_t tamarin_exclude_ac_factors(lean_object *, lean_object *);
uint8_t tamarin_lean_exclude_ac_factors(const whole_word_slice *rows, size_t count,
                                       whole_word_slice heads) {
    return tamarin_exclude_ac_factors(word_rows(rows, count), atom_array(heads.data, heads.size));
}

uint8_t tamarin_lean_check_factors(whole_word_slice decls, const whole_word_slice *rows,
                                   size_t count, whole_word_slice original,
                                   whole_word_slice bindings, whole_word_slice residual) {
    return tamarin_check_factors(atom_array(decls.data, decls.size), word_rows(rows, count),
        atom_array(original.data, original.size), atom_array(bindings.data, bindings.size),
        atom_array(residual.data, residual.size));
}

extern uint8_t tamarin_variant_overlap_agrees(lean_object *decls, lean_object *nodes, lean_object *roots);

uint8_t tamarin_lean_variant_overlap_agrees(whole_word_slice decls, const whole_word_slice *rows,
                                           size_t count, whole_word_slice roots) {
    return tamarin_variant_overlap_agrees(atom_array(decls.data, decls.size), word_rows(rows, count),
        atom_array(roots.data, roots.size));
}

extern lean_object *tamarin_operand_unify(uint64_t width, lean_object *sides);

extern lean_object *tamarin_project_answers(uint64_t width, lean_object *answers);

typedef struct {
    uint8_t status;
    void *arms;
} projected_answers;

/* Transfer the Option.some field's reference to the caller. */
static lean_object *take_some(lean_object *option) {
    lean_object *value = lean_ctor_get(option, 0);
    lean_inc(value);
    lean_dec(option);
    return value;
}

extern lean_object *tamarin_open_match_select(uint64_t rigid, uint64_t subject);

/* Transfer the row array into the same opaque row reader as flat matching. */
static void *wrap_rows(lean_object *rows) {
    lean_object *outer = lean_alloc_array(1, 1);
    lean_array_set_core(outer, 0, rows);
    return outer;
}

/* Interruption of a long search (lean/Tamarin/Interrupt.lean).

   The exports wrapped with an interrupt_watch take a function `poll : Unit -> Bool` and ask it
   before each step of their searches. Their theorems are about a `poll` that is a function, so one
   whose first reply is false replies false every time, and the export then returns the specified
   answer. The closure built here is not a function: it replies true from the moment the caller's
   flag is set or the budget of questions is spent, and from then on every time. The compiled search
   then abandons its loops and returns something unspecified.

   What is trusted here: a reply is handed to the caller only if the closure replied false to every
   question of that call (`stopped` is still 0). Such a run cannot be told from a run with the
   constant function, so its result is the one the theorems describe. Every other reply is released
   unread and the call returns NULL (or status 4), with the reason in `stopped`.

   cancel may be NULL. It is read, never written, and may be set by another thread at any time.
   budget 0 means no limit. asked and stopped are outputs and are reset by every call. */
typedef struct {
    const uint8_t *cancel;
    uint64_t budget;
    uint64_t asked;
    uint8_t stopped;
} interrupt_watch;

/* stopped: the request was cancelled, or the budget of questions is spent. */
#define WATCH_CANCELLED 1
#define WATCH_SPENT 2

static lean_object *watch_poll(lean_object *state, lean_object *unit) {
    interrupt_watch *watch = (interrupt_watch *)((uintptr_t)state & ~(uintptr_t)1);
    (void)unit;
    if (!watch->stopped) {
        watch->asked += 1;
        if (watch->cancel && *(const volatile uint8_t *)watch->cancel) watch->stopped = WATCH_CANCELLED;
        else if (watch->budget && watch->asked > watch->budget) watch->stopped = WATCH_SPENT;
    }
    return lean_box(watch->stopped != 0);
}

/* The closure Lean receives as `poll`. Its captured argument is the address of the watch with the
   low bit set, which Lean's reference counting takes for an unboxed scalar and never follows. The
   closure itself is consumed by the export, and nothing in a reply refers to it. */
static lean_object *watch_closure(interrupt_watch *watch) {
    watch->asked = 0;
    watch->stopped = 0;
    lean_object *closure = lean_alloc_closure((void *)watch_poll, 2, 1);
    lean_closure_set(closure, 0, (lean_object *)((uintptr_t)watch | 1));
    return closure;
}

/* The reply of a watched call, or NULL when the closure ever replied true. */
static void *watched_rows(const interrupt_watch *watch, lean_object *reply) {
    if (watch->stopped) {
        lean_dec(reply);
        return NULL;
    }
    lean_object *outer = lean_alloc_array(1, 1);
    lean_array_set_core(outer, 0, reply);
    return outer;
}

extern lean_object *tamarin_unpack_conjunction(lean_object *, uint64_t, uint64_t, uint64_t);

void *tamarin_lean_unpack_conjunction(const whole_word_slice *rows, size_t count,
                                      uint64_t limit, uint64_t lhs, uint64_t rhs) {
    return wrap_rows(tamarin_unpack_conjunction(word_rows(rows, count), limit, lhs, rhs));
}

extern lean_object *tamarin_total_unify(lean_object *, lean_object *, lean_object *, lean_object *);

extern uint8_t tamarin_certify_table(lean_object *, lean_object *, lean_object *, uint64_t);

/* 1 certifies the table: it decodes, is range restricted, convergent modulo the declared C and AC
   laws and has the finite variant property. 0 carries no information: it is the reply to a
   malformed packet and may be the reply to any table, certified or not. */
uint8_t tamarin_lean_certify_table(whole_word_slice decls, const whole_word_slice *rows,
                                   size_t count, whole_word_slice rules, uint64_t fuel) {
    return tamarin_certify_table(atom_array(decls.data, decls.size), word_rows(rows, count),
                                atom_array(rules.data, rules.size), fuel);
}

extern uint8_t tamarin_factor_refutes(lean_object *, lean_object *, lean_object *);

uint8_t tamarin_lean_factor_refutes(whole_word_slice decls, const whole_word_slice *rows,
                                    size_t count, whole_word_slice equations) {
    return tamarin_factor_refutes(atom_array(decls.data, decls.size), word_rows(rows, count),
                                 atom_array(equations.data, equations.size));
}

/* NULL when the call was interrupted: see interrupt_watch. */
void *tamarin_lean_total_unify(whole_word_slice decls, const whole_word_slice *rows,
                               size_t count, whole_word_slice equations, interrupt_watch *watch) {
    return watched_rows(watch, tamarin_total_unify(watch_closure(watch),
                        atom_array(decls.data, decls.size), word_rows(rows, count),
                        atom_array(equations.data, equations.size)));
}

extern lean_object *tamarin_name_unifiers(lean_object *, lean_object *, lean_object *, lean_object *,
                                          uint8_t, uint8_t);

/* Tables that name the variables a family of unifiers adds to its query. The reply of
   tamarin_lean_total_unify is read through them; no other reading of it is specified.
   names holds two words for each variable row of the request, by the identifier of the row: the
   caller's identifier of the variable's name hint and its index. heads holds the identifier and
   sort words of the query variables in the order of the rows of every arm. ranges holds one row
   for each arm of the reply, with the identifier and sort words of the variables of its range in
   the order of first occurrence. proposal is empty or holds one row for each arm the caller keeps,
   with a hint and an index for each variable of the arm's range. nat is 0 when the caller's module
   has no sort of natural numbers; arms with a variable of that sort then get no table. Without a
   proposal the names have the hint 0 and indices above every index of the query; low lets the
   export use indices the query does not use where none are left above it.
   The reply is {0} (declined) or the status row {1}, the row heads and, for each arm that is kept,
   {arm, (identifier, sort, 0, hint, index | identifier, sort, 1, row, 0)...}: the variable becomes
   the variable with that hint and index, or it stands for the query variable in that row of the arm,
   whose binding is left out. */
void *tamarin_lean_name_unifiers(whole_word_slice names, whole_word_slice heads,
                                 const whole_word_slice *ranges, size_t range_count,
                                 const whole_word_slice *proposal, size_t proposal_count,
                                 uint8_t nat, uint8_t low) {
    return wrap_rows(tamarin_name_unifiers(atom_array(names.data, names.size),
                     atom_array(heads.data, heads.size), word_rows(ranges, range_count),
                     word_rows(proposal, proposal_count), nat != 0, low != 0));
}

extern lean_object *tamarin_apply_names(lean_object *, uint8_t, lean_object *);

/* The reply of tamarin_lean_total_unify read through the tables of tamarin_lean_name_unifiers, in
   words: {0} when there is no reading, or the status row {1} and then, for each arm with a table,
   an empty row and one row {variable row, sort, tokens...} for each query variable the arm binds.
   A token {5 + sort, index, hint} is a variable of the range; the other tokens are those of
   tamarin_lean_total_unify. The caller's reader is tested against this function. */
void *tamarin_lean_apply_names(const whole_word_slice *tables, size_t table_count, uint8_t nat,
                               const whole_word_slice *reply, size_t reply_count) {
    return wrap_rows(tamarin_apply_names(word_rows(tables, table_count), nat != 0,
                                        word_rows(reply, reply_count)));
}

extern lean_object *tamarin_path_reduce(lean_object *, lean_object *, lean_object *, lean_object *,
                                       uint64_t, uint64_t);

/* Reduce on a table that is only range restricted: one rewrite path is followed. The packet is a
   table packet with the term among its rows, and root is its node index. {1, term} is an
   irreducible reduct (not known to be unique), {2} an unsupported table or a reduct that lost a
   sort, {3} a request for more depth, {0} a malformed packet. NULL when the call was
   interrupted: see interrupt_watch. */
void *tamarin_lean_path_reduce(whole_word_slice decls, const whole_word_slice *rows,
                               size_t count, whole_word_slice rules, uint64_t root, uint64_t fuel,
                               interrupt_watch *watch) {
    return watched_rows(watch, tamarin_path_reduce(watch_closure(watch),
                        atom_array(decls.data, decls.size), word_rows(rows, count),
                        atom_array(rules.data, rules.size), root, fuel));
}

extern lean_object *tamarin_total_match(lean_object *, lean_object *, lean_object *, lean_object *);

void *tamarin_lean_total_match(whole_word_slice decls, const whole_word_slice *rows,
                               size_t count, whole_word_slice equations, whole_word_slice bindable) {
    return wrap_rows(tamarin_total_match(atom_array(decls.data, decls.size), word_rows(rows, count),
                                        atom_array(equations.data, equations.size), atom_array(bindable.data, bindable.size)));
}

extern uint8_t tamarin_total_unify_exists(lean_object *, lean_object *, lean_object *, lean_object *);

/* Same packet as tamarin_lean_total_unify. 1: a unifier exists; 2: none exists; 0: malformed packet;
   4: the call was interrupted and decided nothing (see interrupt_watch). */
uint8_t tamarin_lean_total_unify_exists(whole_word_slice decls, const whole_word_slice *rows,
                                        size_t count, whole_word_slice equations,
                                        interrupt_watch *watch) {
    uint8_t reply = tamarin_total_unify_exists(watch_closure(watch),
                        atom_array(decls.data, decls.size), word_rows(rows, count),
                        atom_array(equations.data, equations.size));
    return watch->stopped ? 4 : reply;
}

extern uint8_t tamarin_total_match_exists(lean_object *, lean_object *, lean_object *, lean_object *);

/* 1: a scoped match exists; 2: none exists; 0: malformed packet. */
uint8_t tamarin_lean_total_match_exists(whole_word_slice decls, const whole_word_slice *rows,
                                        size_t count, whole_word_slice equations, whole_word_slice bindable) {
    return tamarin_total_match_exists(atom_array(decls.data, decls.size), word_rows(rows, count),
                                     atom_array(equations.data, equations.size), atom_array(bindable.data, bindable.size));
}

extern lean_object *tamarin_checked_variants(lean_object *, lean_object *, lean_object *, lean_object *, uint64_t);

/* A proposer: a bounded narrowing search. {2} declines. */
void *tamarin_lean_checked_variants(whole_word_slice decls, const whole_word_slice *rows,
                                    size_t count, whole_word_slice rules, whole_word_slice roots, uint64_t fuel) {
    return wrap_rows(tamarin_checked_variants(atom_array(decls.data, decls.size), word_rows(rows, count),
                    atom_array(rules.data, rules.size), atom_array(roots.data, roots.size), fuel));
}

extern lean_object *tamarin_session_reduce(lean_object *, lean_object *, lean_object *, lean_object *,
                                          lean_object *, uint64_t, uint64_t);

/* Reduce on the table that tamarin_lean_certify_table accepted. decls, rows and rules are exactly
   the words of that rules-only packet. The term arrives as further node rows: row i of extra has
   node index count + i, and a child index may name a table row or an earlier further row. root is
   a node index. The reply is {1, term} with the unique normal form, {3} a request for more depth,
   or {0} for a malformed packet. NULL when the call was interrupted: see interrupt_watch. */
void *tamarin_lean_session_reduce(whole_word_slice decls, const whole_word_slice *rows, size_t count,
                                  whole_word_slice rules, const whole_word_slice *extra,
                                  size_t added, uint64_t root, uint64_t fuel,
                                  interrupt_watch *watch) {
    return watched_rows(watch, tamarin_session_reduce(watch_closure(watch),
                        atom_array(decls.data, decls.size), word_rows(rows, count),
                        atom_array(rules.data, rules.size), word_rows(extra, added), root, fuel));
}

extern lean_object *tamarin_session_variant_check(lean_object *, lean_object *, lean_object *,
                                                 lean_object *, lean_object *, lean_object *,
                                                 lean_object *, uint64_t, uint64_t);

/* Check a proposed family of variants on the table that tamarin_lean_certify_table accepted, with
   the observations and the images of the family in further node rows as in
   tamarin_lean_session_reduce. roots are node indices and each family row lists node pairs
   (variable node, image node). The reply has one row: {1} accepted, {2, reason, member} rejected,
   {3} budget exhausted, {0} malformed packet. Only {1} accepts. NULL when the call was
   interrupted: see interrupt_watch. */
void *tamarin_lean_session_variant_check(whole_word_slice decls, const whole_word_slice *rows,
                                         size_t count, whole_word_slice rules,
                                         const whole_word_slice *extra, size_t added,
                                         whole_word_slice roots, const whole_word_slice *family,
                                         size_t members, uint64_t fuel, uint64_t work,
                                         interrupt_watch *watch) {
    return watched_rows(watch, tamarin_session_variant_check(watch_closure(watch),
                        atom_array(decls.data, decls.size),
                        word_rows(rows, count), atom_array(rules.data, rules.size),
                        word_rows(extra, added), atom_array(roots.data, roots.size),
                        word_rows(family, members), fuel, work));
}

/* The tamarin_lean_theory_* functions are the functions above on the packet of the theory of a
   Tamarin file (lean/Tamarin/Theory.lean). Instead of declaration words they take flags (dh 1,
   xor 2, bp 4, mset 8, nat 16), the arities of the other free symbols (ids 16, 17, ...) and the
   number of user AC symbols (ids 16, 17, ...). The rows and rules of a table are the user rules
   only, with node indices from 0; the rules of the enabled builtins are added by Lean. The terms
   of a call on a table are the rows of extra, numbered from 0, and root, roots and the node pairs
   of family index them. Arguments that are not those of a valid signature get the reply to a
   malformed packet. */

extern lean_object *tamarin_theory_unify(lean_object *, uint64_t, lean_object *, uint64_t,
                                         lean_object *, lean_object *);

/* NULL when the call was interrupted: see interrupt_watch. */
void *tamarin_lean_theory_unify(uint64_t flags, whole_word_slice free, uint64_t ac,
                                const whole_word_slice *rows, size_t count,
                                whole_word_slice equations, interrupt_watch *watch) {
    return watched_rows(watch, tamarin_theory_unify(watch_closure(watch), flags,
                        atom_array(free.data, free.size), ac, word_rows(rows, count),
                        atom_array(equations.data, equations.size)));
}

extern uint8_t tamarin_theory_unify_exists(lean_object *, uint64_t, lean_object *, uint64_t,
                                           lean_object *, lean_object *);

/* 1: a unifier exists; 2: none exists; 0: malformed packet; 4: interrupted. */
uint8_t tamarin_lean_theory_unify_exists(uint64_t flags, whole_word_slice free, uint64_t ac,
                                         const whole_word_slice *rows, size_t count,
                                         whole_word_slice equations, interrupt_watch *watch) {
    uint8_t reply = tamarin_theory_unify_exists(watch_closure(watch), flags,
                        atom_array(free.data, free.size), ac, word_rows(rows, count),
                        atom_array(equations.data, equations.size));
    return watch->stopped ? 4 : reply;
}

extern lean_object *tamarin_theory_match(uint64_t, lean_object *, uint64_t, lean_object *,
                                         lean_object *, lean_object *);

void *tamarin_lean_theory_match(uint64_t flags, whole_word_slice free, uint64_t ac,
                                const whole_word_slice *rows, size_t count,
                                whole_word_slice equations, whole_word_slice bindable) {
    return wrap_rows(tamarin_theory_match(flags, atom_array(free.data, free.size), ac,
                     word_rows(rows, count), atom_array(equations.data, equations.size),
                     atom_array(bindable.data, bindable.size)));
}

extern uint8_t tamarin_theory_match_exists(uint64_t, lean_object *, uint64_t, lean_object *,
                                           lean_object *, lean_object *);

/* 1: a scoped match exists; 2: none exists; 0: malformed packet. */
uint8_t tamarin_lean_theory_match_exists(uint64_t flags, whole_word_slice free, uint64_t ac,
                                         const whole_word_slice *rows, size_t count,
                                         whole_word_slice equations, whole_word_slice bindable) {
    return tamarin_theory_match_exists(flags, atom_array(free.data, free.size), ac,
                                       word_rows(rows, count), atom_array(equations.data, equations.size),
                                       atom_array(bindable.data, bindable.size));
}

extern uint8_t tamarin_theory_certify(uint64_t, lean_object *, uint64_t, lean_object *, lean_object *,
                                      uint64_t);

/* 1 certifies the table of the theory, builtin rules and user rules: see
   tamarin_lean_certify_table. */
uint8_t tamarin_lean_theory_certify(uint64_t flags, whole_word_slice free, uint64_t ac,
                                    const whole_word_slice *rows, size_t count,
                                    whole_word_slice rules, uint64_t fuel) {
    return tamarin_theory_certify(flags, atom_array(free.data, free.size), ac, word_rows(rows, count),
                                  atom_array(rules.data, rules.size), fuel);
}

extern lean_object *tamarin_theory_path_reduce(lean_object *, uint64_t, lean_object *, uint64_t,
                                               lean_object *, lean_object *, lean_object *, uint64_t,
                                               uint64_t);

/* Replies as tamarin_lean_path_reduce. NULL when the call was interrupted. */
void *tamarin_lean_theory_path_reduce(uint64_t flags, whole_word_slice free, uint64_t ac,
                                      const whole_word_slice *rows, size_t count,
                                      whole_word_slice rules, const whole_word_slice *extra,
                                      size_t added, uint64_t root, uint64_t fuel,
                                      interrupt_watch *watch) {
    return watched_rows(watch, tamarin_theory_path_reduce(watch_closure(watch), flags,
                        atom_array(free.data, free.size), ac, word_rows(rows, count),
                        atom_array(rules.data, rules.size), word_rows(extra, added), root, fuel));
}

extern lean_object *tamarin_theory_reduce(lean_object *, uint64_t, lean_object *, uint64_t,
                                          lean_object *, lean_object *, lean_object *, uint64_t,
                                          uint64_t);

/* Replies as tamarin_lean_session_reduce, on the table tamarin_lean_theory_certify accepted for
   the same flags, free, ac, rows and rules. NULL when the call was interrupted. */
void *tamarin_lean_theory_reduce(uint64_t flags, whole_word_slice free, uint64_t ac,
                                 const whole_word_slice *rows, size_t count, whole_word_slice rules,
                                 const whole_word_slice *extra, size_t added, uint64_t root,
                                 uint64_t fuel, interrupt_watch *watch) {
    return watched_rows(watch, tamarin_theory_reduce(watch_closure(watch), flags,
                        atom_array(free.data, free.size), ac, word_rows(rows, count),
                        atom_array(rules.data, rules.size), word_rows(extra, added), root, fuel));
}

extern lean_object *tamarin_theory_variant_check(lean_object *, uint64_t, lean_object *, uint64_t,
                                                 lean_object *, lean_object *, lean_object *,
                                                 lean_object *, lean_object *, uint64_t, uint64_t);

/* Replies as tamarin_lean_session_variant_check, on the table tamarin_lean_theory_certify accepted
   for the same flags, free, ac, rows and rules. NULL when the call was interrupted. */
void *tamarin_lean_theory_variant_check(uint64_t flags, whole_word_slice free, uint64_t ac,
                                        const whole_word_slice *rows, size_t count,
                                        whole_word_slice rules, const whole_word_slice *extra,
                                        size_t added, whole_word_slice roots,
                                        const whole_word_slice *family, size_t members,
                                        uint64_t fuel, uint64_t work, interrupt_watch *watch) {
    return watched_rows(watch, tamarin_theory_variant_check(watch_closure(watch), flags,
                        atom_array(free.data, free.size), ac, word_rows(rows, count),
                        atom_array(rules.data, rules.size), word_rows(extra, added),
                        atom_array(roots.data, roots.size), word_rows(family, members), fuel, work));
}

extern lean_object *tamarin_general_variants(lean_object *, lean_object *, lean_object *, lean_object *, uint64_t);

void *tamarin_lean_general_variants(whole_word_slice decls, const whole_word_slice *rows,
                                    size_t count, whole_word_slice rules, whole_word_slice roots, uint64_t fuel) {
    return wrap_rows(tamarin_general_variants(atom_array(decls.data, decls.size), word_rows(rows, count),
                    atom_array(rules.data, rules.size), atom_array(roots.data, roots.size), fuel));
}

extern lean_object *tamarin_fold_variants(lean_object *, lean_object *, lean_object *, lean_object *,
                                         lean_object *, uint64_t, uint64_t);

/* A proposer: folding variant narrowing within `work` narrowing sites. NULL when the call was
   interrupted: see interrupt_watch. */
void *tamarin_lean_fold_variants(whole_word_slice decls, const whole_word_slice *rows,
                                 size_t count, whole_word_slice rules, whole_word_slice roots,
                                 uint64_t fuel, uint64_t work, interrupt_watch *watch) {
    return watched_rows(watch, tamarin_fold_variants(watch_closure(watch),
                        atom_array(decls.data, decls.size), word_rows(rows, count),
                        atom_array(rules.data, rules.size), atom_array(roots.data, roots.size),
                        fuel, work));
}

extern lean_object *tamarin_signed_graph_variants(uint64_t inputs, lean_object *observations);

/* A flat reply is one row of one arm for the existing checked row reader. */
void *tamarin_lean_signed_graph_variants(uint64_t inputs, const whole_word_slice *observations,
                                         size_t count) {
    lean_object *reply = tamarin_signed_graph_variants(inputs, word_rows(observations, count));
    return wrap_rows(wrap_rows(reply));
}

static void *selection_rows(lean_object *reply) {
    return lean_is_scalar(reply) ? NULL : wrap_rows(take_some(reply));
}

extern lean_object *tamarin_binary_cancellation_rows(lean_object *unit);

void *tamarin_lean_binary_cancellation_rows(void) {
    return wrap_rows(tamarin_binary_cancellation_rows(lean_box(0)));
}

extern lean_object *tamarin_mixed_cancellation_rows(lean_object *unit);

void *tamarin_lean_mixed_cancellation_rows(void) {
    return wrap_rows(tamarin_mixed_cancellation_rows(lean_box(0)));
}

extern lean_object *tamarin_xor_matchings(uint64_t width);

void *tamarin_lean_xor_matchings(uint64_t width) {
    return selection_rows(tamarin_xor_matchings(width));
}

extern lean_object *tamarin_dh_exponent_images(lean_object *unit);

void *tamarin_lean_dh_exponent_images(void) {
    return wrap_rows(tamarin_dh_exponent_images(lean_box(0)));
}

void *tamarin_lean_open_match_select(uint64_t rigid, uint64_t subject) {
    return selection_rows(tamarin_open_match_select(rigid, subject));
}

extern lean_object *tamarin_dh_tower_images(uint64_t width);

void *tamarin_lean_dh_tower_images(uint64_t width) {
    return selection_rows(tamarin_dh_tower_images(width));
}

extern lean_object *tamarin_ac_pivot(uint64_t size);

void *tamarin_lean_ac_pivot(uint64_t size) {
    return selection_rows(tamarin_ac_pivot(size));
}

extern lean_object *tamarin_dh_peer_images(uint8_t power);

void *tamarin_lean_dh_peer_images(void) {
    return selection_rows(tamarin_dh_peer_images(1));
}

extern uint8_t tamarin_reduction_graph(lean_object *rows);

uint8_t tamarin_lean_reduction_graph(const whole_word_slice *rows, size_t count) {
    return tamarin_reduction_graph(word_rows(rows, count));
}

extern lean_object *tamarin_ac_subgroups(uint64_t size);

void *tamarin_lean_ac_subgroups(uint64_t size) {
    return selection_rows(tamarin_ac_subgroups(size));
}

extern lean_object *tamarin_sorted_ac_match(uint64_t ac_sort, lean_object *variable_sorts,
                                          lean_object *atom_sorts, lean_object *occurrences,
                                          lean_object *tail, lean_object *rhs);

void *tamarin_lean_sorted_ac_match(uint64_t ac_sort, whole_word_slice variable_sorts,
                                   whole_word_slice atom_sorts, whole_word_slice occurrences,
                                   whole_word_slice tail, whole_word_slice rhs) {
    lean_object *reply = tamarin_sorted_ac_match(ac_sort, atom_array(variable_sorts.data, variable_sorts.size),
        atom_array(atom_sorts.data, atom_sorts.size), atom_array(occurrences.data, occurrences.size),
        atom_array(tail.data, tail.size), atom_array(rhs.data, rhs.size));
    return lean_is_scalar(reply) ? NULL : take_some(reply);
}

/* Solver deferral and invalid solver output have distinct statuses. A
 * successful projection transfers one array reference, even for zero arms. */
static projected_answers project_answers(uint64_t width, lean_object *option) {
    if (lean_is_scalar(option)) return (projected_answers){0, NULL};
    lean_object *projected = tamarin_project_answers(width, take_some(option));
    if (lean_is_scalar(projected)) return (projected_answers){255, NULL};
    return (projected_answers){1, take_some(projected)};
}

projected_answers tamarin_lean_operand_unify(uint64_t width, const whole_word_slice *sides, size_t count) {
    return project_answers(width, tamarin_operand_unify(width, word_rows(sides, count)));
}

extern lean_object *tamarin_masked_operand_unify(uint64_t width, uint64_t mask, lean_object *sides);

projected_answers tamarin_lean_masked_operand_unify(uint64_t width, uint64_t mask,
                                                    const whole_word_slice *sides, size_t count) {
    return project_answers(width, tamarin_masked_operand_unify(width, mask, word_rows(sides, count)));
}

size_t tamarin_lean_match_row_size(const void *result, size_t arm, size_t index) {
    if (arm >= tamarin_lean_match_count(result)) return SIZE_MAX;
    lean_object *rows = lean_array_get_core((lean_object *)result, arm);
    if (index >= lean_array_size(rows)) return SIZE_MAX;
    return lean_array_size(lean_array_get_core(rows, index));
}
