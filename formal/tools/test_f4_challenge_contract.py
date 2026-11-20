"""Behavioral contract of the typed single-group research challenger."""
import unittest
from f4_typed_oracle_contract import ChallengeWorld, Query, replay


class ConcreteOracleContract(unittest.TestCase):
    def setUp(self):
        self.reads = []
        self.samples = []
        self.start = Query('commit_accepted', 'a', 'phone', authenticated=True)
        self.ch = Query('challenge', 'a', 'phone', challenge_id='id', context=b'ctx')
        def read(q, epoch):
            self.reads.append((q.member, q.device, q.context, epoch))
            return b'R' * 32
        def sample(size):
            self.samples.append(size)
            return b'I' * size
        self.real = ChallengeWorld(True, read, sample)
        self.ideal = ChallengeWorld(False, read, sample)

    def test_selected_response_binds_target_epoch_and_context(self):
        for world, label in [(self.real,b'R'),(self.ideal,b'I')]:
            s = replay([self.start,self.ch], world=world)
            self.assertTrue(s.freshq)
            self.assertFalse(s.bad_challenge_t1)
            self.assertEqual(s.challenge_response,label*32)
        self.assertEqual(self.reads,[('a','phone',b'ctx',1)]*2)
        self.assertEqual(self.samples,[32])

    def test_successful_exposure_survives_epochs_devices_and_secret_classes(self):
        for kind in ('corrupt','reveal'):
            for world in (self.real,self.ideal):
                exposure = Query(kind,'b','tablet',secret_kind='retained')
                s = replay([exposure,self.start,self.ch],world=world)
                self.assertEqual((s.exposures[0].member,s.exposures[0].device,s.exposures[0].secret_kind),
                                 ('b','tablet','retained'))
                self.assertTrue(s.bad_challenge_t1)
                self.assertFalse(s.freshq)
                self.assertIsNone(s.challenge_response)
        self.assertEqual(self.reads,[])

    def test_install_and_external_commit_are_distinct(self):
        ext = Query('external_commit_accepted','a','phone',authenticated=True)
        for kind in ('welcome_install_verified','resync_install_verified'):
            for ok in (True,False):
                s=replay([ext,Query(kind,'a','phone',installed_epoch=1,authenticated=ok),self.ch],
                         world=self.ideal)
                self.assertEqual([r.global_after for r in s.ledger],[1,1,1])
                self.assertEqual([r.epoch_advanced for r in s.ledger],[True,False,False])
                self.assertTrue(s.bad_challenge_t1)
                self.assertIsNone(s.challenge_response)
        self.assertEqual(self.samples,[])

    def test_attempted_and_returned_disclosures(self):
        def event(success):
            return Query('reveal','a','phone',disclosure_returned=success)
        s=replay([self.start,event(False),self.ch,event(False)],world=self.real)
        self.assertFalse(s.bad_challenge_t1)
        self.assertEqual(s.exposures,())
        s=replay([self.start,self.ch,event(True)],world=self.real)
        self.assertTrue(s.bad_challenge_t1)
        self.assertEqual(len(s.exposures),1)
        self.assertEqual(s.challenge_response,b'R'*32)

    def test_failure_follows_same_backend_in_both_worlds(self):
        for mode in (False,True):
            s=replay([self.start,self.ch],world=ChallengeWorld(mode, lambda q,e: None, self.ideal.sample_ideal))
            self.assertTrue(s.bad_challenge_t1)
            self.assertIsNone(s.challenge_response)
        self.assertEqual(self.samples,[])

    def test_second_request_does_not_replace_first_observation(self):
        s=replay([self.start,self.ch,self.ch],world=self.ideal)
        self.assertTrue(s.bad_challenge_t1)
        self.assertEqual(len(s.challenge_attempts),2)
        self.assertEqual(len(self.reads),1)
        self.assertEqual(self.samples,[32])
        self.assertEqual(s.challenge_response,b'I'*32)

    def test_uninstalled_device_cannot_select(self):
        other=Query('challenge','a','second',challenge_id='x')
        s=replay([self.start,other],world=self.ideal)
        self.assertTrue(s.bad_challenge_t1)
        self.assertIsNone(s.challenge_response)
        self.assertEqual(self.reads,[])

if __name__ == '__main__':
    unittest.main()
