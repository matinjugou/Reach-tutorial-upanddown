'reach 0.1';

const [ isHand, Up, Down ] = makeEnum(2);
const [ isOutcome, A_WINS, B_WINS, C_WINS, DRAW ] = makeEnum(4);

const winner = (handA, handB, handC) => {
  const sum = handA + handB + handC;
  if (sum == 1) return handA == 1 ? A_WINS : (handB == 1 ? B_WINS : C_WINS)
  else if (sum == 2) return handA == 0 ? A_WINS : (handB == 0 ? B_WINS : C_WINS)
  else return DRAW;
}

const Player =
      { ...hasRandom,
        getHand: Fun([], UInt),
        seeOutcome: Fun([UInt], Null),
        informTimeout: Fun([], Null) };
const Deployer =
      { ...Player,
        wager: UInt };
const Attacher =
      { ...Player,
        acceptWager: Fun([UInt], Null) };

const DEADLINE = 20;
export const main =
  Reach.App(
    {},
    [Participant('Alice', Deployer), Participant('Bob', Attacher), Participant('Charles', Attacher)],
    (A, B, C) => {
      const informTimeout = () => {
        each([A, B, C], () => {
          interact.informTimeout(); }); };

      A.only(() => {
        const wager = declassify(interact.wager); });
      A.publish(wager).pay(wager);
      commit();

      B.only(() => {
        interact.acceptWager(wager); });
      B.pay(wager).timeout(DEADLINE, () => closeTo(A, informTimeout));
      commit();

      C.only(() => {
        interact.acceptWager(wager); });
      C.pay(wager).timeout(DEADLINE, () => {
        race(A, B).publish();
        transfer(wager).to(A);
        transfer(wager).to(B);
        commit();
        exit();
      });

      var outcome = DRAW;
      invariant(balance() == 3 * wager && isOutcome(outcome) );
      while ( outcome == DRAW ) {
        commit();

        A.only(() => {
          const _handA = interact.getHand();
          const [_commitA, _saltA] = makeCommitment(interact, _handA);
          const commitA = declassify(_commitA); });
        A.publish(commitA).timeout(DEADLINE, () => {
          race(B, C).publish();
          transfer(balance() / 2).to(B);
          transfer(balance()).to(C);
          commit();
          exit();
        });
        commit();

        unknowable(B, A(_handA, _saltA));
        B.only(() => {
          const _handB = interact.getHand();
          const [_commitB, _saltB] = makeCommitment(interact, _handB);
          const commitB = declassify(_commitB); });
        B.publish(commitB).timeout(DEADLINE, () => {
          race(A, C).publish();
          transfer(balance() / 2).to(A);
          transfer(balance()).to(C);
          commit();
          exit();
        });
        commit();

        unknowable(C, A(_handA, _saltA));
        unknowable(C, B(_handB, _saltB));
        C.only(() => {
          const handC = declassify(interact.getHand()); });
        C.publish(handC).timeout(DEADLINE, () => {
          race(A, B).publish();
          transfer(balance() / 2).to(A);
          transfer(balance()).to(B);
          commit();
          exit();
        });
        commit();

        A.only(() => {
          const [saltA, handA] = declassify([_saltA, _handA]); });
        A.publish(saltA, handA).timeout(DEADLINE, () => {
          race(B, C).publish();
          transfer(balance() / 2).to(B);
          transfer(balance()).to(C);
          commit();
          exit();
        });;
        checkCommitment(commitA, saltA, handA);
        commit();

        B.only(() => {
          const [saltB, handB] = declassify([_saltB, _handB]); });
        B.publish(saltB, handB).timeout(DEADLINE, () => {
          race(A, C).publish();
          transfer(balance() / 2).to(A);
          transfer(balance()).to(C);
          commit();
          exit();
        });
        checkCommitment(commitB, saltB, handB);

        outcome = winner(handA, handB, handC);
        continue; }

      assert(outcome == A_WINS || outcome == B_WINS || outcome == C_WINS);
      transfer(3 * wager).to(outcome == A_WINS ? A : (outcome == B_WINS ? B : C));
      commit();

      each([A, B, C], () => {
        interact.seeOutcome(outcome); });
      exit(); });
