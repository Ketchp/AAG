#ifndef __PROGTEST__
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <deque>
#include <functional>
#include <iomanip>
#include <iostream>
#include <list>
#include <map>
#include <memory>
#include <numeric>
#include <optional>
#include <queue>
#include <set>
#include <sstream>
#include <stack>
#include <vector>

using namespace std;
using Symbol = char;
using Word = std::vector<Symbol>;

struct Grammar {
    std::set<Symbol> m_Nonterminals;
    std::set<Symbol> m_Terminals;
    std::vector<std::pair<Symbol, std::vector<Symbol>>> m_Rules;
    Symbol m_InitialSymbol;
};
#endif


template<typename T_it>
class Enumerate_const_iterator {
public:
    using T_val = typename std::iterator_traits<T_it>::value_type;

    explicit Enumerate_const_iterator(T_it it)
        : Enumerate_const_iterator(it, 0) {};

    Enumerate_const_iterator(T_it it, size_t start)
        : it(it), idx(start) {};

    bool operator!=(const Enumerate_const_iterator &other) {
        return it != other.it;
    }

    Enumerate_const_iterator &operator++() {
        it++; idx++;
        return *this;
    }

    std::pair<size_t, T_val> operator*() {
        return std::make_pair(idx, *it);
    }
private:
    T_it it;
    size_t idx = 0;
};


template<typename T_C>
class Const_Enum_Wrapper {
public:
    using T_it = decltype(std::begin(std::declval<const T_C &>()));
    explicit Const_Enum_Wrapper(const T_C &val)
        : cont(val) {}

    [[nodiscard]] Enumerate_const_iterator<T_it> begin() const {
        return Enumerate_const_iterator(std::begin(cont));
    }

    [[nodiscard]] Enumerate_const_iterator<T_it> end() const {
        return Enumerate_const_iterator(std::end(cont));
    }
private:
    const T_C &cont;
};

template<typename T_Cont>
Const_Enum_Wrapper<T_Cont> enumerate(const T_Cont &cont) {
    return Const_Enum_Wrapper(cont);
}

std::vector<size_t> trace(const Grammar& G, const Word& W) {
    size_t n = W.size();
    const auto &rules = G.m_Rules;

    if(n == 0) {
        for(const auto &[rule_idx, rule]: enumerate(rules)) {
            const auto &[from, to] = rule;
            if(from == G.m_InitialSymbol && to.empty())
                return {rule_idx};
        }
        return {};
    }

    // [string size][string offset][symbol] -> (rule idx to follow, size of first symbol expanded)
    vector<vector<map<Symbol, pair<size_t, size_t>>>>
        T(n, vector<map<Symbol, pair<size_t, size_t>>>(n));

    for(const auto &[w_pos, symbol]: enumerate(W)) {
        for(const auto &[rule_idx, rule]: enumerate(rules)) {
            const auto &[from, to] = rule;
            if(to.size() != 1 || to[0] != symbol) continue;
            T[0][w_pos][from] = {rule_idx, 0};
        }
    }

    for(size_t w_len = 2; w_len <= n; w_len++) {
        for(size_t start = 0; start + w_len <= n; start++) {
            for(size_t part_len = 1; part_len < w_len; part_len++) {
                for(const auto &[rule_idx, rule]: enumerate(rules)) {
                    const auto &[from, to] = rule;
                    if(to.size() <= 1) continue;

                    const auto &f_part = T[part_len - 1][start];
                    const auto &s_part = T[w_len - part_len - 1][start + part_len];
                    auto &current = T[w_len - 1][start];

                    if(!f_part.contains(to[0])) continue;
                    if(!s_part.contains(to[1])) continue;

                    current[from] = {rule_idx, part_len};
                }
            }
        }
    }

    const auto &T_init = T[n-1][0];
    if(!T_init.contains(G.m_InitialSymbol))
        return {};


    //         rule_no, first size, second size, offset
    vector<tuple<size_t, size_t, size_t, size_t>> stack;
    {
        auto [rule_no, f_size] = T_init.at(G.m_InitialSymbol);
        stack.emplace_back(rule_no, f_size, n - f_size, 0);
    }

    vector<size_t> ret;
    while(!stack.empty()) {
        auto [rule_no, f_size, s_size, f_start] = stack.back();
        stack.pop_back();
        ret.emplace_back(rule_no);

        auto rule_dest = rules[rule_no].second;
        if(rule_dest.size() == 1) {
            assert(f_size == 0);
            continue;
        }

        Symbol s1 = rule_dest[0];
        Symbol s2 = rule_dest[1];

        auto s_start = f_start + f_size;

        auto [f_rule, f_f_size] = T[f_size - 1][f_start].at(s1);
        auto [s_rule, s_f_size] = T[s_size - 1][s_start].at(s2);

        stack.emplace_back(s_rule, s_f_size, s_size - s_f_size, s_start);
        stack.emplace_back(f_rule, f_f_size, f_size - f_f_size, f_start);
    }

    return ret;
}

#ifndef __PROGTEST__
int main()
{
    Grammar g0{
        {'A', 'B', 'C', 'S'},
        {'a', 'b'},
        {
            {'S', {'A', 'B'}},
            {'S', {'B', 'C'}},
            {'A', {'B', 'A'}},
            {'A', {'a'}},
            {'B', {'C', 'C'}},
            {'B', {'b'}},
            {'C', {'A', 'B'}},
            {'C', {'a'}},
        },
        'S'};

    assert(trace(g0, {'b', 'a', 'a', 'b', 'a'}) == std::vector<size_t>({0, 2, 5, 3, 4, 6, 3, 5, 7}));
    assert(trace(g0, {'b'}) == std::vector<size_t>({}));
    assert(trace(g0, {'a'}) == std::vector<size_t>({}));
    assert(trace(g0, {}) == std::vector<size_t>({}));
    assert(trace(g0, {'a', 'a', 'a', 'a', 'a'}) == std::vector<size_t>({1, 4, 6, 3, 4, 7, 7, 7, 7}));
    assert(trace(g0, {'a', 'b'}) == std::vector<size_t>({0, 3, 5}));
    assert(trace(g0, {'b', 'a'}) == std::vector<size_t>({1, 5, 7}));
    assert(trace(g0, {'c', 'a'}) == std::vector<size_t>({}));

    Grammar g1{
        {'A', 'B'},
        {'x', 'y'},
        {
            {'A', {}},
            {'A', {'x'}},
            {'B', {'x'}},
            {'A', {'B', 'B'}},
            {'B', {'B', 'B'}},
        },
        'A'};

    assert(trace(g1, {}) == std::vector<size_t>({0}));
    assert(trace(g1, {'x'}) == std::vector<size_t>({1}));
    assert(trace(g1, {'x', 'x'}) == std::vector<size_t>({3, 2, 2}));
    assert(trace(g1, {'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 2, 2, 2}));
    assert(trace(g1, {'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 2, 2, 2, 2}));
    assert(trace(g1, {'x', 'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 4, 2, 2, 2, 2, 2}));
    assert(trace(g1, {'x', 'x', 'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2}));
    assert(trace(g1, {'x', 'x', 'x', 'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2}));
    assert(trace(g1, {'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2}));
    assert(trace(g1, {'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x', 'x'}) == std::vector<size_t>({3, 4, 4, 4, 4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2}));

    Grammar g2{
        {'A', 'B'},
        {'x', 'y'},
        {
            {'A', {'x'}},
            {'B', {'x'}},
            {'A', {'B', 'B'}},
            {'B', {'B', 'B'}},
        },
        'B'};

    assert(trace(g2, {}) == std::vector<size_t>({}));
    assert(trace(g2, {'x'}) == std::vector<size_t>({1}));
    assert(trace(g2, {'x', 'x'}) == std::vector<size_t>({3, 1, 1}));
    assert(trace(g2, {'x', 'x', 'x'}) == std::vector<size_t>({3, 3, 1, 1, 1}));

    Grammar g3{
        {'A', 'B', 'C', 'D', 'E', 'S'},
        {'a', 'b'},
        {
            {'S', {'A', 'B'}},
            {'S', {'S', 'S'}},
            {'S', {'a'}},
            {'A', {'B', 'S'}},
            {'A', {'C', 'D'}},
            {'A', {'b'}},
            {'B', {'D', 'D'}},
            {'B', {'b'}},
            {'C', {'D', 'E'}},
            {'C', {'b'}},
            {'C', {'a'}},
            {'D', {'a'}},
            {'E', {'S', 'S'}},
        },
        'S'};

    assert(trace(g3, {}) == std::vector<size_t>({}));
    assert(trace(g3, {'b'}) == std::vector<size_t>({}));
    assert(trace(g3, {'a', 'b', 'a', 'a', 'b'}) == std::vector<size_t>({1, 2, 0, 3, 7, 1, 2, 2, 7}));
    assert(trace(g3, {'a', 'b', 'a', 'a', 'b', 'a', 'b', 'a', 'b', 'a', 'a'}) == std::vector<size_t>({1, 1, 0, 4, 8, 11, 12, 0, 5, 6, 11, 11, 0, 4, 9, 11, 7, 11, 7, 2, 2}));
}
#endif

