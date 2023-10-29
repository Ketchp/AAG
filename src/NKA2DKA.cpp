#include <vector>
#include <map>
#include <set>
#include <iostream>
#include <ranges>
#include <sstream>
#include <iomanip>
#include <format>


/**

 NFA  a   b   c    d
>0   0   0   0|1  -
 1   -   2   1|4  0
<2   1   -   3    1
 3   -   4   -    2
<4   4   -   -    3

 */


template<class T>
ssize_t sz(const T &t) {
    return static_cast<ssize_t>(t.size());
}

template<class T>
auto it_exc_last(const T &t) {
    return std::ranges::take_view{t, sz(t) - 1};
}


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


enum class State: char {};
enum class Symbol: char {};

template<typename T>
struct State_set: public std::set<T> {
    using T_self = State_set<T>;
    using std::set<T>::set;

    bool operator<(const T_self &o) const {
        if(this->size() < o.size()) return true;
        if(o.size() < this->size()) return false;
        return static_cast<const std::set<T> &>(*this) < (o);
    }
};


std::ostream &operator<<(std::ostream &os, const State &s) {
    return os << static_cast<const char>(s);
}

std::ostream &operator<<(std::ostream &os, const std::set<State> &s) {
    os << '{';
    for(const auto &state: it_exc_last(s))
        os << state << ", ";
    os << *s.rbegin();
    return os << '}';
}

std::ostream &operator<<(std::ostream &os, const Symbol &s) {
    return os << static_cast<char>(s);
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
using T_KA = std::tuple<T_transitions<T_state, T_symbol, T_destination>,
                      T_start<T_state>,
                      T_end<T_state>>;

template<typename T_state, typename T_symbol>
using T_NKA = T_KA<T_state, T_symbol, T_states<T_state>>;

template<typename T_state, typename T_symbol>
using T_DKA = T_KA<T_state, T_symbol, T_state>;


template<typename T_state = int, typename T_symbol = char>
struct NKA: public T_NKA<T_state, T_symbol> {
    using T_NKA<T_state, T_symbol>::T_NKA;
};

template<typename T_state = int, typename T_symbol = char>
struct DKA: public T_DKA<T_state, T_symbol> {
    using self = DKA<T_state,T_symbol>;
    using T_DKA<T_state, T_symbol>::T_DKA;

    template<typename T, typename B>
    friend std::ostream &operator<<(std::ostream &os, const DKA<T, B> &);
};


template<typename T_state, typename T_symbol>
std::ostream &operator<<(std::ostream &os, const DKA<T_state, T_symbol> &dka) {
    const auto &transitions = std::get<0>(dka);
    const auto &start = std::get<1>(dka);
    const auto &end = std::get<2>(dka);

    int state_w = 1;
    std::set<T_symbol> symbols;
    std::map<T_state, int> states;
    int idx = 0;
    for(const auto &[state, trans]: transitions) {
        for(auto [symbol, dst]: trans) {
            symbols.emplace(std::move(symbol));
            if(states.find(dst) == states.end())
                states.emplace(std::move(dst), idx++);
        }
        std::stringstream ss;
        ss << state;
        state_w = std::max(state_w, static_cast<int>(ss.str().size()));
    }

    os << std::setw(state_w) << std::right << "State";

    for(const auto &symbol: symbols)
        os << " | " << symbol;
    os << '\n';

    for(const auto &[state, trans]: transitions) {
//        os << states[state] << ' ';
        if(end.count(state)) {
            os << '<';
            if(start.count(state)) os << '-';
        }
        if(start.count(state)) os << '>';


        os << state << "-> ";
        os << '{';
        for(const auto &symbol: symbols) {
            os << symbol << ": ";
            if(trans.contains(symbol))
                os << trans.at(symbol);
            os << ", ";
        }
        os << "},\n";
    }

    return os;
}



NKA<State, Symbol> input
{
    {
        {State{'A'},
            {
                {Symbol{'a'}, {State{'A'}, State{'C'}, State{'F'}}},
                {Symbol{'b'}, {State{'B'}}},
                {Symbol{'e'}, {State{'C'}}},
            }
        },
        {State{'B'},
         {
                 {Symbol{'a'}, {State{'B'}, State{'D'}}},
            }
        },
        {State{'D'},
            {
                 {Symbol{'a'}, {State{'A'}, State{'F'}}},
                 {Symbol{'b'}, {State{'C'}, State{'D'}}},
                 {Symbol{'e'}, {State{'A'}}},
            }
        },
    },
    {State{'A'}, State{'D'}},
    {State{'A'}, State{'C'},}
};


template<typename T_state, typename T_symbol>
DKA<State_set<T_state>, T_symbol> nka2dka(const NKA<T_state, T_symbol> &nka) {
    using T_state_nka = T_state;
    using T_state_dka = State_set<T_state>;

    using T_transition_dka = T_transition<T_symbol, T_state_dka>;

    const T_transitions<T_state, T_symbol, T_states<T_state>> &nka_trans = std::get<0>(nka);
    const auto &nka_starts = std::get<1>(nka);
    const auto &nka_ends = std::get<2>(nka);

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


int main() {
    auto res = nka2dka(input);

    std::cout << res;

    return 0;
}