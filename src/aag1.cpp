#ifndef __PROGTEST__
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <sstream>

#include <algorithm>
#include <deque>
#include <list>
#include <map>
#include <queue>
#include <set>
#include <stack>
#include <vector>

#include <cassert>
using namespace std;

using State = unsigned int;
using Symbol = char;

struct MISNFA {
    std::set<State> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<State, Symbol>, std::set<State>> m_Transitions;
    std::set<State> m_InitialStates;
    std::set<State> m_FinalStates;
};

struct DFA {
    std::set<State> m_States;
    std::set<Symbol> m_Alphabet;
    std::map<std::pair<State, Symbol>, State> m_Transitions;
    State m_InitialState;
    std::set<State> m_FinalStates;

    bool operator==(const DFA& other) const
    {
        std::map<State, State> state_map;
        state_map[m_InitialState] = other.m_InitialState;
        std::vector<State> to_do; to_do.emplace_back(m_InitialState);

        while(!to_do.empty()) {
            const auto my_t = to_do.back();
            const auto &other_t = state_map[my_t];
            to_do.pop_back();

            for(const auto &symbol: m_Alphabet) {
                if(!m_Transitions.contains({my_t, symbol})) {
                    if(other.m_Transitions.contains({other_t, symbol}))
                        return false;
                    continue;
                }
                if(!other.m_Transitions.contains({other_t, symbol}))
                    return false;

                const auto &my_dest = m_Transitions.at({my_t, symbol});
                const auto &other_dest = other.m_Transitions.at({other_t, symbol});

                if(state_map.contains(my_dest)) {
                    if(state_map[my_dest] != other_dest)
                        return false;
                    continue;
                }
                to_do.emplace_back(my_dest);
                state_map.emplace(my_dest, other_dest);
            }
        }

        std::set<State> mapped_final;
        for(const auto &f: m_FinalStates)
            mapped_final.emplace(state_map.at(f));

        return mapped_final == other.m_FinalStates;
    }
};

#endif

//#include "ka_transformations.cpp"
#ifndef __PROGTEST__
#include <iostream>
#include <sstream>

#include <algorithm>
#include <deque>
#include <list>
#include <map>
#include <set>
#include <vector>
#endif


namespace AAG {
    template<typename T_state_new = int>
    struct Namer {
        using T_name = T_state_new;
        T_name state{};
        T_name new_state() {return state++;}
    };

    template <typename T>
    bool have_common_element(const std::set<T> &a, const std::set<T> &b) {
        auto first1 = a.begin(), first2 = b.begin();
        const auto last1 = a.end(), last2 = b.end();

        while (first1 != last1 && first2 != last2) {
            if (*first1 < *first2)
                ++first1;
            else if (*first2 < *first1)
                ++first2;
            else
                return true;
        }
        return false;
    }

    template<typename T_symbol>
    struct EpsilonSymbol: public std::pair<T_symbol, bool> {
        using std::pair<T_symbol, bool>::pair;
        explicit EpsilonSymbol(T_symbol symbol): std::pair<T_symbol, bool>(symbol, false) {}

        static EpsilonSymbol epsilon() {
            return EpsilonSymbol();
        };

        [[nodiscard]] T_symbol remove_epsilon() const { return this->first; }

        [[nodiscard]] bool is_epsilon() const { return this->second; }

        template <typename T_s>
        friend std::ostream &operator<<(std::ostream &os, const EpsilonSymbol<T_s> &);
    private:
        EpsilonSymbol(): std::pair<T_symbol, bool>({}, true) {};
    };

    template <typename T>
    concept EpsilonSymbolLike = requires(T t) { t.is_epsilon(); };

    template <typename T_symbol>
    std::ostream &operator<<(std::ostream &os, const EpsilonSymbol<T_symbol> &symbol) {
        if(symbol.second) os << '_';
        else os << symbol.first;
        return os;
    }

    template<typename T>
    struct State_set: public std::set<T> {
        using T_self = State_set<T>;
        using std::set<T>::set;

        using std::set<T>::merge;

        void merge(const State_set &other) {
            merge(static_cast<std::set<T>>(other));
        }

        bool operator<(const T_self &o) const {
            if(this->size() < o.size()) return true;
            if(o.size() < this->size()) return false;
            return static_cast<const std::set<T> &>(*this) < (o);
        }
    };

    template<typename T_state>
    std::ostream &operator<<(std::ostream &os, const std::set<T_state> &s) {
        os << '{';
        for(auto it = s.begin();
            it != s.end() && ++it != s.end();
            it++) {
            it--;
            os << *it << ", ";
        }
        if(!s.empty())
            os << *s.rbegin();
        return os << '}';
    }

    template<typename T_state>
    using T_states = State_set<T_state>;

    template<typename T_symbol, typename T_destination>
    using T_transition = std::map<T_symbol, T_destination>;

    template<typename T_state, typename T_symbol, typename T_destination = T_state>
    using T_transitions = std::map<T_state, T_transition<T_symbol, T_destination>>;

    template<typename T_state>
    using T_start = T_states<T_state>;

    template<typename T_state>
    using T_end = T_states<T_state>;

    template<typename T_state, typename T_symbol, typename T_destination>
    class KA: public std::tuple<T_transitions<T_state, T_symbol, T_destination>,
            T_start<T_state>,
            T_end<T_state>> {
        using T_transitions_KA = T_transitions<T_state, T_symbol, T_destination>;
        using std::tuple<T_transitions_KA,
                T_start<T_state>,
                T_end<T_state>>::tuple;
    public:
        auto &
        transitions()
        { return std::get<0>(*this); };

        [[nodiscard]] const auto &
        transitions() const
        { return std::get<0>(*this); };

        auto &
        start_states()
        { return std::get<1>(*this); };

        [[nodiscard]] const auto &
        start_states() const
        { return std::get<1>(*this); };

        auto &
        end_states()
        { return std::get<2>(*this); };

        [[nodiscard]] const auto &
        end_states() const
        { return std::get<2>(*this); };

        template<typename T_S, typename T_A, typename T_D>
        friend std::ostream &operator<<(std::ostream &os, const KA<T_S, T_A, T_D> &);
    };

    template<typename T_state, typename T_symbol, typename T_dest>
    std::ostream &operator<<(std::ostream &os, const KA<T_state, T_symbol, T_dest> &ka) {
        const auto &starts = ka.start_states();
        const auto &ends = ka.end_states();
        const auto &transitions = ka.transitions();

        std::set<T_symbol> symbols;
        for(const auto &[state, trans]: transitions)
            for(const auto &[symbol, d]: trans)
                symbols.emplace(symbol);

        for(const auto &[state, trans]: transitions) {
            os << (ends.contains(state) ? '<' : ' ');
            os << '-';
            os << (starts.contains(state) ? '>' : ' ');

            os << state << "=> ";
            for(const auto &s: symbols) {
                if(!trans.contains(s))
                    continue;
                os << s << ':' << trans.at(s) << ", ";
            }

            os << '\n';
        }

        return os;
    }


    template<typename T_state, typename T_symbol>
    using T_NKA = KA<T_state, T_symbol, T_states<T_state>>;

    template<typename T_state, typename T_symbol>
    using T_DKA = KA<T_state, T_symbol, T_state>;


    template<typename T_state = int, typename T_symbol = char>
    struct NKA: public T_NKA<T_state, T_symbol> {
        using T_NKA<T_state, T_symbol>::T_NKA;
    };

    template<typename T_state, EpsilonSymbolLike T_symbol>
    struct NKAe: public NKA<T_state, T_symbol> {
        [[nodiscard]] T_states<T_state>
        epsilon_closure(
                const T_state &from_state) const
        {
            T_states<T_state> closure;
            std::set<T_state> to_do;
            to_do.emplace(from_state);
            const auto &trans = this->transitions();

            while(!to_do.empty()) {
                const auto c = to_do.extract(to_do.begin()).value();
                closure.insert(c);

                if(!trans.contains(c)) continue;
                for(const auto &[symbol, destinations]: trans.at(c)) {
                    if(!symbol.is_epsilon()) continue;
                    to_do.insert(destinations.begin(), destinations.end());
                }
            }

            return closure;
        }
    };

    template <typename G>
    concept StateGenerator = requires(G g) {
        typename G::T_name;
        { g.new_state() } -> std::same_as<typename G::T_name>;
    };

    template<typename T_state = int, typename T_symbol = char>
    struct DKA: public T_DKA<T_state, T_symbol> {
        using T_DKA<T_state, T_symbol>::T_DKA;

        template<StateGenerator G>
        DKA<typename G::T_name, T_symbol> rename_states(G g) {
            using T_state_new = G::T_name;
            DKA<T_state_new, T_symbol> renamed;

            std::map<T_state, T_state_new> mapping;
            auto get_state = [&mapping, &g](const T_state &st) {
                if(mapping.contains(st)) return mapping.at(st);
                return mapping.emplace(st, g.new_state()).first->second;
            };

            for(const auto &start: this->start_states())
                renamed.start_states().emplace(get_state(start));

            for(const auto &start: this->end_states())
                renamed.end_states().emplace(get_state(start));

            for(const auto &[state, trans]: this->transitions()){
                const auto &ns = get_state(state);
                for(const auto &[symbol, dest]: trans) {
                    renamed.transitions()[ns].emplace(symbol, get_state(dest));
                }
            }

            return renamed;
        }

    };


    template<typename T_state, typename T_symbol, typename T_state_DKA = State_set<T_state>>
    DKA<T_state_DKA, T_symbol>
    nka2dka(
            const NKA<T_state, T_symbol> &nka)
    {
        using T_state_nka = T_state;
        using T_state_dka = State_set<T_state>;

        using T_transition_dka = T_transition<T_symbol, T_state_dka>;

        const T_transitions<T_state, T_symbol, T_states<T_state>> &nka_trans = nka.transitions();
        const auto &nka_starts = nka.start_states();
        const auto &nka_ends = nka.end_states();

        T_states<T_state_dka> dka_starts;
        T_states<T_state_dka> dka_ends;

        for(T_state_nka start: nka_starts)
            dka_starts.emplace(T_state_dka{std::move(start)});

        T_transitions<T_state_dka, T_symbol> transitions_dka;

        std::vector<T_state_dka> to_process(dka_starts.begin(), dka_starts.end());

        while(!to_process.empty()) {
            T_state_dka from = std::move(to_process.back());
            to_process.pop_back();

            if(have_common_element(nka_ends, from))
                dka_ends.emplace(from);

            T_transition_dka trans_dka;

            for(const T_state_nka &from_nka: from) {
                if(!nka_trans.contains(from_nka)) continue;
                for(const auto &[symbol, dest]: nka_trans.at(from_nka)) {
                    trans_dka[symbol].insert(dest.begin(), dest.end());
                }
            }

            for(const auto &[symbol, to]: trans_dka) {
                if(from == to) continue;
                if(transitions_dka.find(to) != transitions_dka.end()) continue;
                to_process.emplace_back(to);
            }

            transitions_dka[from] = trans_dka;
        }

        return {transitions_dka, dka_starts, dka_ends};
    }

    template<typename T_state, typename T_symbol>
    NKAe<T_state, EpsilonSymbol<T_symbol>>
    remove_multiple_start(
            const NKA<T_state, T_symbol> &nka,
            T_state new_start)
    {
        NKAe<T_state, EpsilonSymbol<T_symbol>> out;
        out.end_states() = nka.end_states();

        if(nka.start_states().size() > 1){
            const auto epsilon = EpsilonSymbol<T_symbol>::epsilon();

            out.transitions()[new_start][epsilon] = nka.start_states();

            out.start_states().emplace(std::move(new_start));
        }
        else
            out.start_states() = nka.start_states();

        for(const auto &[state, trans]: nka.transitions())
            for(const auto &[symbol, destination]: trans)
                out.transitions()[state][EpsilonSymbol{symbol}] = destination;

        return out;
    }

    template<typename T_state, typename T_symbol>
    NKA<T_state, T_symbol>
    remove_epsilon(
            const NKAe<T_state, EpsilonSymbol<T_symbol>> &nka_e)
    {
        NKA<T_state, T_symbol> out;
        const auto &in_trans = nka_e.transitions();
        auto &out_trans = out.transitions();

        out.start_states() = nka_e.start_states();
        out.end_states() = nka_e.end_states();

        for(const auto &[state, trans]: in_trans) {
            for(const auto &[e_symbol, dest]: trans) {
                if(!e_symbol.is_epsilon())
                    out_trans[state][e_symbol.remove_epsilon()] = dest;
            }
            const auto closure = nka_e.epsilon_closure(state);
            if(have_common_element(closure, nka_e.end_states())) {
                out.end_states().emplace(state);
            }

            for(const auto &ng_state: closure) {
                if(!in_trans.contains(ng_state))
                    continue;
                for(const auto &[symbol, dest]: in_trans.at(ng_state)) {
                    if(symbol.is_epsilon()) continue;
                    out_trans[state][symbol.remove_epsilon()].merge(dest);
                }
            }
        }

        return out;
    }

    template<typename T_state, typename T_symbol>
    NKA<T_state, T_symbol> NKA_reverse(const NKA<T_state, T_symbol> &orig) {
        NKA<T_state, T_symbol> reversed;

        const auto &ot = orig.transitions();
        auto &rt = reversed.transitions();

        reversed.end_states() = orig.start_states();

        std::vector<T_state> to_do(orig.start_states().begin(),
                                   orig.start_states().end());
        std::set<T_state> done;

        while(!to_do.empty()) {
            const auto current = to_do.back();
            done.emplace(current);
            to_do.pop_back();

            if(orig.end_states().contains(current))
                reversed.start_states().emplace(current);

            if(!ot.contains(current))
                continue;

            for(const auto &[symbol, destinations]: ot.at(current))
                for(const auto &dest: destinations) {
                    rt[dest][symbol].emplace(current);
                    if(!done.contains(dest))
                        to_do.emplace_back(dest);
                }
        }
        return reversed;
    }

    template<typename T_state, typename T_symbol>
    NKA<T_state, T_symbol>
    NKA_remove_useless_unreachable(const NKA<T_state, T_symbol> &orig) {
        return NKA_reverse(NKA_reverse(orig));
    }
}


namespace AAG_symbols {
    enum class State: unsigned int {};
    enum class Symbol: char {};

    std::ostream &operator<<(std::ostream &os, const State &s) {
        return os << static_cast<std::underlying_type_t<const State>>(s);
    }

    std::ostream &operator<<(std::ostream &os, const Symbol &s) {
        return os << static_cast<char>(s);
    }
}

template <typename T_state, typename T_symbol>
auto MISNFA2NKA(const MISNFA &nfa) {
    using namespace AAG;
    NKA<T_state, T_symbol> better_structure;

    for(const auto &[state_symbol, destination]: nfa.m_Transitions) {
        const auto &[state, symbol] = state_symbol;
        for(const auto &e: destination)
            better_structure.transitions()[T_state{state}][T_symbol{symbol}].emplace(T_state{e});

    }

    for(const auto &s: nfa.m_InitialStates)
        better_structure.start_states().emplace(T_state{s});

    for(const auto &s: nfa.m_FinalStates)
        better_structure.end_states().emplace(T_state{s});

    return better_structure;
}


DFA determinize(const MISNFA& nfa) {
    using namespace AAG;
    long new_s = *std::max_element(nfa.m_States.begin(), nfa.m_States.end());

    auto res = MISNFA2NKA<long, char>(nfa);

    auto res_w_uu = AAG::NKA_remove_useless_unreachable(res);

    auto nka_eps = AAG::remove_multiple_start(res_w_uu, new_s + 1);

    auto nka = remove_epsilon(nka_eps);

    auto dka = nka2dka(nka);

    auto renamed = dka.rename_states(Namer<State>{});

    DFA out;

    out.m_InitialState = *renamed.start_states().begin();
    out.m_FinalStates = renamed.end_states();

    out.m_Alphabet = nfa.m_Alphabet;

    auto &states = out.m_States;
    states.emplace(out.m_InitialState);
    states.insert(out.m_FinalStates.begin(), out.m_FinalStates.end());

    for(const auto &[state, trans]: renamed.transitions()) {
        states.emplace(state);
        for(const auto &[symbol, dest]: trans) {
            out.m_Transitions.emplace(std::make_pair(state, symbol), dest);
            states.emplace(dest);
        }
    }
    return out;
}



#ifndef __PROGTEST__
MISNFA t0 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10},
    {'h', 'm', 'q'},
    {
            {{1, 'h'}, {4}},
            {{1, 'm'}, {3}},
            {{1, 'q'}, {2}},
            {{2, 'h'}, {0}},
            {{2, 'm'}, {0}},
            {{2, 'q'}, {0}},
            {{3, 'q'}, {4}},
            {{4, 'h'}, {7}},
            {{4, 'm'}, {0}},
            {{4, 'q'}, {8}},
            {{5, 'q'}, {9}},
            {{6, 'h'}, {5}},
            {{6, 'm'}, {8}},
            {{6, 'q'}, {6}},
            {{7, 'h'}, {7}},
            {{7, 'q'}, {8}},
            {{9, 'q'}, {4}},
            {{10, 'h'}, {0}},
            {{10, 'm'}, {0}},
            {{10, 'q'}, {0}},
    },
    {1},
    {0, 5, 6}
};

MISNFA t1 = {
    {0},
    {'a'},
    {},
    {0},
    {0}
};

MISNFA t2 = {
    {0, 1, 2},
    {'a', 'b'},
    {
        {{0, 'a'}, {2}}
    },
    {0, 1},
    {1, 2}
};


MISNFA in0 = {
    {0, 1, 2},
    {'e', 'l'},
    {
        {{0, 'e'}, {1}},
        {{0, 'l'}, {1}},
        {{1, 'e'}, {2}},
        {{2, 'e'}, {0}},
        {{2, 'l'}, {2}},
    },
    {0},
    {1, 2},
};
DFA out0 = {
    {0, 1, 2},
    {'e', 'l'},
    {
        {{0, 'e'}, 1},
        {{0, 'l'}, 1},
        {{1, 'e'}, 2},
        {{2, 'e'}, 0},
        {{2, 'l'}, 2},
    },
    0,
    {1, 2},
};
MISNFA in1 = {
    {0, 1, 2, 3},
    {'g', 'l'},
    {
        {{0, 'g'}, {1}},
        {{0, 'l'}, {2}},
        {{1, 'g'}, {3}},
        {{1, 'l'}, {3}},
        {{2, 'g'}, {1}},
        {{2, 'l'}, {0}},
        {{3, 'l'}, {1}},
    },
    {0},
    {0, 2, 3},
};
DFA out1 = {
    {0, 1, 2, 3},
    {'g', 'l'},
    {
        {{0, 'g'}, 1},
        {{0, 'l'}, 2},
        {{1, 'g'}, 3},
        {{1, 'l'}, 3},
        {{2, 'g'}, 1},
        {{2, 'l'}, 0},
        {{3, 'l'}, 1},
    },
    0,
    {0, 2, 3},
};
MISNFA in2 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12},
    {'l', 'm'},
    {
        {{0, 'l'}, {1}},
        {{0, 'm'}, {2}},
        {{1, 'l'}, {3}},
        {{2, 'l'}, {4}},
        {{2, 'm'}, {5}},
        {{3, 'l'}, {3}},
        {{4, 'l'}, {3}},
        {{4, 'm'}, {6}},
        {{5, 'l'}, {7}},
        {{5, 'm'}, {6}},
        {{6, 'l'}, {7}},
        {{6, 'm'}, {8}},
        {{7, 'l'}, {9}},
        {{7, 'm'}, {10}},
        {{8, 'l'}, {6}},
        {{8, 'm'}, {10}},
        {{9, 'l'}, {7}},
        {{9, 'm'}, {8}},
        {{10, 'l'}, {11}},
        {{10, 'm'}, {4}},
        {{11, 'l'}, {12}},
        {{11, 'm'}, {9}},
        {{12, 'l'}, {6}},
        {{12, 'm'}, {10}},
    },
    {0},
    {1, 3},
};
DFA out2 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12},
    {'l', 'm'},
    {
        {{0, 'l'}, 1},
        {{0, 'm'}, 2},
        {{1, 'l'}, 3},
        {{2, 'l'}, 4},
        {{2, 'm'}, 5},
        {{3, 'l'}, 3},
        {{4, 'l'}, 3},
        {{4, 'm'}, 6},
        {{5, 'l'}, 7},
        {{5, 'm'}, 6},
        {{6, 'l'}, 7},
        {{6, 'm'}, 8},
        {{7, 'l'}, 9},
        {{7, 'm'}, 10},
        {{8, 'l'}, 6},
        {{8, 'm'}, 10},
        {{9, 'l'}, 7},
        {{9, 'm'}, 8},
        {{10, 'l'}, 11},
        {{10, 'm'}, 4},
        {{11, 'l'}, 12},
        {{11, 'm'}, 9},
        {{12, 'l'}, 6},
        {{12, 'm'}, 10},
    },
    0,
    {1, 3},
};
MISNFA in3 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
    {'a', 'b'},
    {
        {{0, 'a'}, {1}},
        {{0, 'b'}, {2}},
        {{1, 'a'}, {3}},
        {{1, 'b'}, {4}},
        {{2, 'a'}, {5}},
        {{2, 'b'}, {6}},
        {{3, 'a'}, {7}},
        {{3, 'b'}, {8}},
        {{4, 'a'}, {9}},
        {{5, 'a'}, {5}},
        {{5, 'b'}, {10}},
        {{6, 'a'}, {8}},
        {{6, 'b'}, {8}},
        {{7, 'a'}, {11}},
        {{8, 'a'}, {3}},
        {{8, 'b'}, {9}},
        {{9, 'a'}, {5}},
        {{9, 'b'}, {5}},
        {{10, 'a'}, {1}},
        {{10, 'b'}, {2}},
        {{11, 'a'}, {5}},
        {{11, 'b'}, {5}},
    },
    {0},
    {5, 6},
};
DFA out3 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
    {'a', 'b'},
    {
        {{0, 'a'}, 1},
        {{0, 'b'}, 2},
        {{1, 'a'}, 3},
        {{1, 'b'}, 4},
        {{2, 'a'}, 5},
        {{2, 'b'}, 6},
        {{3, 'a'}, 7},
        {{3, 'b'}, 8},
        {{4, 'a'}, 9},
        {{5, 'a'}, 5},
        {{5, 'b'}, 10},
        {{6, 'a'}, 8},
        {{6, 'b'}, 8},
        {{7, 'a'}, 11},
        {{8, 'a'}, 3},
        {{8, 'b'}, 9},
        {{9, 'a'}, 5},
        {{9, 'b'}, 5},
        {{10, 'a'}, 1},
        {{10, 'b'}, 2},
        {{11, 'a'}, 5},
        {{11, 'b'}, 5},
    },
    0,
    {5, 6},
};
MISNFA in4 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
    {'e', 'j', 'k'},
    {
        {{0, 'e'}, {1}},
        {{0, 'j'}, {2}},
        {{0, 'k'}, {3}},
        {{1, 'e'}, {2}},
        {{1, 'j'}, {4}},
        {{1, 'k'}, {5}},
        {{2, 'e'}, {6}},
        {{2, 'j'}, {0}},
        {{2, 'k'}, {4}},
        {{3, 'e'}, {7}},
        {{3, 'j'}, {2}},
        {{3, 'k'}, {1}},
        {{4, 'e'}, {4}},
        {{4, 'j'}, {8}},
        {{4, 'k'}, {7}},
        {{5, 'e'}, {4}},
        {{5, 'j'}, {0}},
        {{5, 'k'}, {4}},
        {{6, 'e'}, {7}},
        {{6, 'j'}, {8}},
        {{6, 'k'}, {4}},
        {{7, 'e'}, {3}},
        {{7, 'j'}, {1}},
        {{7, 'k'}, {8}},
        {{8, 'e'}, {2}},
        {{8, 'j'}, {4}},
        {{8, 'k'}, {9}},
        {{9, 'e'}, {4}},
        {{9, 'j'}, {0}},
        {{9, 'k'}, {4}},
    },
    {0},
    {1, 6, 8},
};
DFA out4 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9},
    {'e', 'j', 'k'},
    {
        {{0, 'e'}, 1},
        {{0, 'j'}, 2},
        {{0, 'k'}, 3},
        {{1, 'e'}, 2},
        {{1, 'j'}, 4},
        {{1, 'k'}, 5},
        {{2, 'e'}, 6},
        {{2, 'j'}, 0},
        {{2, 'k'}, 4},
        {{3, 'e'}, 7},
        {{3, 'j'}, 2},
        {{3, 'k'}, 1},
        {{4, 'e'}, 4},
        {{4, 'j'}, 8},
        {{4, 'k'}, 7},
        {{5, 'e'}, 4},
        {{5, 'j'}, 0},
        {{5, 'k'}, 4},
        {{6, 'e'}, 7},
        {{6, 'j'}, 8},
        {{6, 'k'}, 4},
        {{7, 'e'}, 3},
        {{7, 'j'}, 1},
        {{7, 'k'}, 8},
        {{8, 'e'}, 2},
        {{8, 'j'}, 4},
        {{8, 'k'}, 9},
        {{9, 'e'}, 4},
        {{9, 'j'}, 0},
        {{9, 'k'}, 4},
    },
    0,
    {1, 6, 8},
};
MISNFA in5 = {
    {0, 1, 2, 3},
    {'e', 'n', 'r'},
    {
        {{0, 'e'}, {1}},
        {{0, 'n'}, {1}},
        {{0, 'r'}, {2}},
        {{1, 'e'}, {2}},
        {{1, 'n'}, {3}},
        {{1, 'r'}, {3}},
        {{2, 'e'}, {3}},
        {{2, 'n'}, {3}},
        {{2, 'r'}, {1}},
        {{3, 'e'}, {1}},
        {{3, 'n'}, {1}},
        {{3, 'r'}, {2}},
    },
    {0},
    {0, 3},
};
DFA out5 = {
    {0, 1, 2, 3},
    {'e', 'n', 'r'},
    {
        {{0, 'e'}, 1},
        {{0, 'n'}, 1},
        {{0, 'r'}, 2},
        {{1, 'e'}, 2},
        {{1, 'n'}, 3},
        {{1, 'r'}, 3},
        {{2, 'e'}, 3},
        {{2, 'n'}, 3},
        {{2, 'r'}, 1},
        {{3, 'e'}, 1},
        {{3, 'n'}, 1},
        {{3, 'r'}, 2},
    },
    0,
    {0, 3},
};
MISNFA in6 = {
    {0, 1, 2, 3, 4, 5, 6, 7},
    {'e', 't', 'x'},
    {
        {{0, 'e'}, {1}},
        {{0, 't'}, {2}},
        {{0, 'x'}, {3}},
        {{1, 'e'}, {1}},
        {{1, 't'}, {4}},
        {{1, 'x'}, {5}},
        {{2, 'e'}, {3}},
        {{2, 't'}, {6}},
        {{2, 'x'}, {2}},
        {{3, 'e'}, {3}},
        {{3, 't'}, {7}},
        {{3, 'x'}, {4}},
        {{4, 'e'}, {4}},
        {{4, 't'}, {4}},
        {{4, 'x'}, {7}},
        {{5, 'e'}, {5}},
        {{5, 't'}, {5}},
        {{5, 'x'}, {5}},
        {{6, 'e'}, {5}},
        {{6, 't'}, {2}},
        {{6, 'x'}, {0}},
        {{7, 'e'}, {5}},
        {{7, 't'}, {5}},
        {{7, 'x'}, {5}},
    },
    {0},
    {0, 3},
};
DFA out6 = {
    {0, 1, 2, 3},
    {'e', 't', 'x'},
    {
        {{0, 't'}, 1},
        {{0, 'x'}, 2},
        {{1, 'e'}, 2},
        {{1, 't'}, 3},
        {{1, 'x'}, 1},
        {{2, 'e'}, 2},
        {{3, 't'}, 1},
        {{3, 'x'}, 0},
    },
    0,
    {0, 2},
};
MISNFA in7 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10},
    {'d', 'm', 't'},
    {
        {{0, 'd'}, {2}},
        {{0, 'm'}, {0}},
        {{0, 't'}, {3}},
        {{1, 'd'}, {9}},
        {{1, 'm'}, {0}},
        {{1, 't'}, {2}},
        {{2, 'd'}, {3}},
        {{2, 'm'}, {7}},
        {{4, 'd'}, {7}},
        {{4, 'm'}, {1}},
        {{5, 'd'}, {5}},
        {{5, 'm'}, {5}},
        {{5, 't'}, {0}},
        {{6, 'd'}, {7}},
        {{8, 'm'}, {7}},
        {{8, 't'}, {7}},
        {{9, 'd'}, {7}},
        {{9, 'm'}, {1}},
        {{10, 'd'}, {7}},
    },
    {1},
    {0, 5, 6, 10},
};
DFA out7 = {
    {0, 1, 2},
    {'d', 'm', 't'},
    {
        {{0, 'd'}, 1},
        {{0, 'm'}, 2},
        {{1, 'm'}, 0},
        {{2, 'm'}, 2},
    },
    0,
    {2},
};
MISNFA in8 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10},
    {'h', 'm', 'q'},
    {
        {{1, 'h'}, {4}},
        {{1, 'm'}, {3}},
        {{1, 'q'}, {2}},
        {{2, 'h'}, {0}},
        {{2, 'm'}, {0}},
        {{2, 'q'}, {0}},
        {{3, 'q'}, {4}},
        {{4, 'h'}, {7}},
        {{4, 'm'}, {0}},
        {{4, 'q'}, {8}},
        {{5, 'q'}, {9}},
        {{6, 'h'}, {5}},
        {{6, 'm'}, {8}},
        {{6, 'q'}, {6}},
        {{7, 'h'}, {7}},
        {{7, 'q'}, {8}},
        {{9, 'q'}, {4}},
        {{10, 'h'}, {0}},
        {{10, 'm'}, {0}},
        {{10, 'q'}, {0}},
    },
    {1},
    {0, 5, 6},
};
DFA out8 = {
    {0, 1, 2, 3, 4},
    {'h', 'm', 'q'},
    {
        {{0, 'h'}, 1},
        {{0, 'm'}, 2},
        {{0, 'q'}, 3},
        {{1, 'm'}, 4},
        {{2, 'q'}, 1},
        {{3, 'h'}, 4},
        {{3, 'm'}, 4},
        {{3, 'q'}, 4},
    },
    0,
    {4},
};
MISNFA in9 = {
    {0, 1, 2, 3, 4},
    {'h', 'l', 'w'},
    {
        {{0, 'l'}, {1, 2, 3}},
        {{0, 'w'}, {4}},
        {{1, 'h'}, {1}},
        {{1, 'l'}, {3, 4}},
        {{1, 'w'}, {0, 2}},
        {{2, 'h'}, {3}},
        {{2, 'l'}, {1}},
        {{2, 'w'}, {0}},
        {{3, 'h'}, {3}},
        {{3, 'l'}, {0, 3}},
        {{3, 'w'}, {0, 2}},
        {{4, 'l'}, {1, 2, 3}},
        {{4, 'w'}, {4}},
    },
    {1},
    {0, 1, 2, 3, 4},
};
DFA out9 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13},
    {'h', 'l', 'w'},
    {
        {{0, 'h'}, 0},
        {{0, 'l'}, 1},
        {{0, 'w'}, 2},
        {{1, 'h'}, 3},
        {{1, 'l'}, 4},
        {{1, 'w'}, 5},
        {{2, 'h'}, 3},
        {{2, 'l'}, 6},
        {{2, 'w'}, 7},
        {{3, 'h'}, 3},
        {{3, 'l'}, 8},
        {{3, 'w'}, 2},
        {{4, 'h'}, 9},
        {{4, 'l'}, 10},
        {{4, 'w'}, 5},
        {{5, 'h'}, 3},
        {{5, 'l'}, 6},
        {{5, 'w'}, 7},
        {{6, 'h'}, 9},
        {{6, 'l'}, 11},
        {{6, 'w'}, 2},
        {{7, 'l'}, 6},
        {{7, 'w'}, 12},
        {{8, 'h'}, 3},
        {{8, 'l'}, 4},
        {{8, 'w'}, 5},
        {{9, 'h'}, 9},
        {{9, 'l'}, 13},
        {{9, 'w'}, 2},
        {{10, 'h'}, 9},
        {{10, 'l'}, 10},
        {{10, 'w'}, 5},
        {{11, 'h'}, 9},
        {{11, 'l'}, 10},
        {{11, 'w'}, 5},
        {{12, 'l'}, 6},
        {{12, 'w'}, 12},
        {{13, 'h'}, 3},
        {{13, 'l'}, 4},
        {{13, 'w'}, 5},
    },
    0,
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13},
};
MISNFA in10 = {
    {0, 1, 2, 3, 4, 5, 6},
    {'j', 'k', 'w'},
    {
        {{0, 'j'}, {0, 5}},
        {{0, 'k'}, {1, 2}},
        {{0, 'w'}, {2}},
        {{1, 'j'}, {0, 1, 2}},
        {{1, 'k'}, {4, 5}},
        {{1, 'w'}, {2}},
        {{2, 'j'}, {0, 1, 2}},
        {{2, 'w'}, {0}},
        {{3, 'j'}, {0, 2}},
        {{3, 'k'}, {4, 6}},
        {{3, 'w'}, {0}},
        {{4, 'j'}, {5}},
        {{5, 'j'}, {5}},
        {{6, 'j'}, {0, 2}},
        {{6, 'k'}, {3, 4}},
        {{6, 'w'}, {0}},
    },
    {2},
    {0, 1, 3, 6},
};
DFA out10 = {
    {0, 1, 2, 3, 4, 5, 6, 7},
    {'j', 'k', 'w'},
    {
        {{0, 'j'}, 1},
        {{0, 'w'}, 2},
        {{1, 'j'}, 3},
        {{1, 'k'}, 4},
        {{1, 'w'}, 5},
        {{2, 'j'}, 6},
        {{2, 'k'}, 7},
        {{2, 'w'}, 0},
        {{3, 'j'}, 3},
        {{3, 'k'}, 4},
        {{3, 'w'}, 5},
        {{4, 'j'}, 3},
        {{4, 'w'}, 5},
        {{5, 'j'}, 3},
        {{5, 'k'}, 7},
        {{5, 'w'}, 5},
        {{6, 'j'}, 6},
        {{6, 'k'}, 7},
        {{6, 'w'}, 0},
        {{7, 'j'}, 1},
        {{7, 'w'}, 5},
    },
    0,
    {1, 2, 3, 4, 5, 6, 7},
};
MISNFA in11 = {
    {0, 1, 2, 3, 4, 5, 6},
    {'b', 'i', 'r'},
    {
        {{0, 'b'}, {2}},
        {{0, 'i'}, {1, 2, 4}},
        {{0, 'r'}, {0}},
        {{1, 'b'}, {1, 2, 5}},
        {{1, 'i'}, {0}},
        {{1, 'r'}, {1, 6}},
        {{2, 'b'}, {2, 4}},
        {{2, 'r'}, {1, 2}},
        {{3, 'b'}, {2}},
        {{3, 'i'}, {2}},
        {{3, 'r'}, {1, 3, 4}},
        {{4, 'r'}, {6}},
        {{5, 'b'}, {2}},
        {{5, 'i'}, {1, 2, 4}},
        {{5, 'r'}, {0}},
        {{6, 'r'}, {6}},
    },
    {1},
    {0, 1, 2, 5},
};
DFA out11 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
    {'b', 'i', 'r'},
    {
        {{0, 'b'}, 1},
        {{0, 'i'}, 2},
        {{0, 'r'}, 3},
        {{1, 'b'}, 4},
        {{1, 'i'}, 5},
        {{1, 'r'}, 6},
        {{2, 'b'}, 7},
        {{2, 'i'}, 8},
        {{2, 'r'}, 2},
        {{3, 'b'}, 1},
        {{3, 'i'}, 2},
        {{3, 'r'}, 3},
        {{4, 'b'}, 4},
        {{4, 'i'}, 5},
        {{4, 'r'}, 6},
        {{5, 'b'}, 4},
        {{5, 'i'}, 5},
        {{5, 'r'}, 6},
        {{6, 'b'}, 4},
        {{6, 'i'}, 5},
        {{6, 'r'}, 6},
        {{7, 'b'}, 9},
        {{7, 'r'}, 10},
        {{8, 'b'}, 4},
        {{8, 'i'}, 2},
        {{8, 'r'}, 11},
        {{9, 'b'}, 9},
        {{9, 'r'}, 11},
        {{10, 'b'}, 4},
        {{10, 'i'}, 2},
        {{10, 'r'}, 11},
        {{11, 'b'}, 4},
        {{11, 'i'}, 2},
        {{11, 'r'}, 11},
    },
    0,
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11},
};
MISNFA in12 = {
    {0, 1, 2, 3, 4, 5, 6},
    {'l', 'q', 't'},
    {
        {{0, 'l'}, {2, 4, 5}},
        {{0, 'q'}, {2}},
        {{0, 't'}, {1}},
        {{1, 'l'}, {0, 2}},
        {{1, 'q'}, {1, 4}},
        {{1, 't'}, {0, 2}},
        {{2, 'l'}, {5}},
        {{2, 'q'}, {0, 4}},
        {{2, 't'}, {0}},
        {{3, 'l'}, {3, 4}},
        {{3, 'q'}, {0}},
        {{3, 't'}, {0, 2}},
        {{4, 't'}, {4}},
        {{5, 'l'}, {0, 2}},
        {{5, 'q'}, {4, 5}},
        {{5, 't'}, {0, 2}},
        {{6, 'l'}, {4, 6}},
        {{6, 'q'}, {0}},
        {{6, 't'}, {0, 2}},
    },
    {2, 4},
    {0, 1, 3, 5, 6},
};
DFA out12 = {
    {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18},
    {'l', 'q', 't'},
    {
        {{0, 'l'}, 1},
        {{0, 'q'}, 2},
        {{0, 't'}, 2},
        {{1, 'l'}, 3},
        {{1, 'q'}, 4},
        {{1, 't'}, 3},
        {{2, 'l'}, 5},
        {{2, 'q'}, 6},
        {{2, 't'}, 7},
        {{3, 'l'}, 5},
        {{3, 'q'}, 8},
        {{3, 't'}, 9},
        {{4, 'l'}, 3},
        {{4, 'q'}, 4},
        {{4, 't'}, 8},
        {{5, 'l'}, 10},
        {{5, 'q'}, 11},
        {{5, 't'}, 8},
        {{6, 'l'}, 1},
        {{6, 'q'}, 2},
        {{6, 't'}, 12},
        {{7, 'l'}, 3},
        {{7, 'q'}, 7},
        {{7, 't'}, 8},
        {{8, 'l'}, 5},
        {{8, 'q'}, 8},
        {{8, 't'}, 13},
        {{9, 'l'}, 14},
        {{9, 'q'}, 15},
        {{9, 't'}, 16},
        {{10, 'l'}, 14},
        {{10, 'q'}, 14},
        {{10, 't'}, 16},
        {{11, 'l'}, 14},
        {{11, 'q'}, 5},
        {{11, 't'}, 17},
        {{12, 'l'}, 5},
        {{12, 'q'}, 6},
        {{12, 't'}, 18},
        {{13, 'l'}, 14},
        {{13, 'q'}, 15},
        {{13, 't'}, 17},
        {{14, 'l'}, 14},
        {{14, 'q'}, 14},
        {{14, 't'}, 17},
        {{15, 'l'}, 10},
        {{15, 'q'}, 13},
        {{15, 't'}, 8},
        {{16, 'l'}, 14},
        {{16, 'q'}, 17},
        {{16, 't'}, 16},
        {{17, 'l'}, 14},
        {{17, 'q'}, 17},
        {{17, 't'}, 17},
        {{18, 'l'}, 3},
        {{18, 'q'}, 7},
        {{18, 't'}, 3},
    },
    0,
    {1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18},
};
MISNFA in13 = {
    {0, 1, 2, 3, 4, 5, 6},
    {'o', 'r'},
    {
        {{0, 'o'}, {0, 1, 4}},
        {{0, 'r'}, {5}},
        {{1, 'o'}, {4}},
        {{1, 'r'}, {2}},
        {{2, 'o'}, {0, 1}},
        {{2, 'r'}, {0, 5}},
        {{3, 'r'}, {2, 5}},
        {{5, 'o'}, {0, 1}},
        {{5, 'r'}, {0, 5}},
        {{6, 'r'}, {2}},
    },
    {2, 5},
    {0},
};
DFA out13 = {
    {0, 1, 2, 3},
    {'o', 'r'},
    {
        {{0, 'o'}, 1},
        {{0, 'r'}, 2},
        {{1, 'o'}, 3},
        {{1, 'r'}, 0},
        {{2, 'o'}, 3},
        {{2, 'r'}, 2},
        {{3, 'o'}, 3},
        {{3, 'r'}, 0},
    },
    0,
    {1, 2, 3},
};

template <typename T>
std::ostream &operator<<(std::ostream &os, const std::set<T> &cset) {
    os << '{';
    for(auto it = cset.begin();
        it != cset.end() && ++it != cset.end();
        it++) {
        it--;
        os << *it << ", ";
    }
    if(!cset.empty())
        os << *cset.rbegin();
    return os << '}';
}

std::ostream &operator<<(std::ostream &os, const DFA &mfa) {
    os << mfa.m_Alphabet << '\n';
    os << mfa.m_States << '\n';
    os << mfa.m_InitialState << " > " << mfa.m_FinalStates <<'\n';

    std::map<State, std::map<char, State>> brp;

    for(const auto &[pp, to]: mfa.m_Transitions) {
        const auto &[from, symbol] = pp;
        brp[from].emplace(symbol, to);
    }

    for(const auto &[from, trans]: brp) {
        os << from << ": ";
        for(const auto &[symbol, to]: trans) {
            os << symbol << ": " << to << ", ";
        }
        os << '\n';
    }
    return os;
}


void test(auto in, auto ref) {
    if(in == ref)
        return;
    std::cout << in << std::endl;
    std::cout << std::string(50, '=') << std::endl;
    std::cout << ref << std::endl;

    assert(false);
}

int main()
{
    std::cout << MISNFA2NKA<long, char>(t2) << std::endl;
    std::cout << determinize(t2) << std::endl;
    test(determinize(in1), out1);
    test(determinize(in2), out2);
    test(determinize(in3), out3);
    test(determinize(in4), out4);
    test(determinize(in5), out5);
    test(determinize(in6), out6);
    test(determinize(in7), out7);
    test(determinize(in8), out8);
    test(determinize(in9), out9);
    test(determinize(in10), out10);
    test(determinize(in11), out11);
    test(determinize(in12), out12);
    test(determinize(in13), out13);

    return 0;
}
#endif
